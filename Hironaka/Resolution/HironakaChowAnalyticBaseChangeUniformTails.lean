import Hironaka.Resolution.HironakaActualAnalyticBaseChangeCoefficients
import Hironaka.Resolution.HironakaActualAnalyticBaseRescaling
import Hironaka.Resolution.HironakaChowFibreLiftUniformTails

/-! Genuine SAME-family analytic base-change uniform tails. No target data,
division, flatness or remainder-naturality packet is supplied. BP FIRST:
hironaka-g10-analytic-base-change-uniform-tails.tex. -/
set_option autoImplicit false
open Set Metric Filter Classical
open scoped Topology
namespace Hironaka.HironakaChowAnalyticBaseChangeUniformTails
noncomputable section
open HolGerm HironakaRelativeNormalIdeal HironakaActualCentreJointJets
  HironakaActualJointBaseFibre HironakaActualWeightedVertexSmallTails
  HironakaActualFiniteDegLexWeights HironakaActualWeightedScaling
  HironakaChowFibreLiftWeightedFactors HironakaChowFibreLiftUniformTails
  HironakaActualAnalyticBaseChangeCoefficients HironakaActualAnalyticBaseRescaling
  HironakaActualCauchyCoordinateDivision HironakaHolomorphicJetChartInvariance
  HironakaActualRelativeCoefficientGerms HironakaActualCoefficientPresentationCentrePower

/-- The actual WHOLE fibre image stays exactly the ORIGINAL ideal. -/
theorem base_changed_fibre_ideal_eq (d e t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t))))
    (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0) :
    Ideal.map (jointBaseZeroTrace e t).toRingHom
      (Ideal.map (jointBasePullback d e t φ hφ hφ0).toRingHom I) =
      Ideal.map (jointBaseZeroTrace d t).toRingHom I := by
  rw [Ideal.map_map]
  apply congrArg (fun f : HolGerm (ComplexModel (d+t)) →+* HolGerm (ComplexModel t) => Ideal.map f I)
  apply RingHom.ext
  exact jointBaseZeroTrace_jointBasePullback d e t φ hφ hφ0

/-- Native equality transport retains EVERY original normal exponent. -/
def fibreVertexEquiv {t : ℕ} {J K : Ideal (HolGerm (ComplexModel t))} (h : K = J) :
    ActualVertexIndex t K ≃ ActualVertexIndex t J := by
  subst K
  exact Equiv.refl _

/-- Transport the ENTIRE actual fibre data, without choosing a new generator. -/
def transportFibreData {t : ℕ} {J K : Ideal (HolGerm (ComplexModel t))} (h : K = J)
    (G : ActualWeightedVertexGermData t J) : ActualWeightedVertexGermData t K := by
  subst K
  exact G

private theorem fibreVertexEquiv_val {t : ℕ} {J K : Ideal (HolGerm (ComplexModel t))}
    (h : K = J) (a : ActualVertexIndex t K) : (fibreVertexEquiv h a).val = a.val := by
  subst K
  rfl

private theorem transport_degree {t : ℕ} {J K : Ideal (HolGerm (ComplexModel t))}
    (h : K = J) (G : ActualWeightedVertexGermData t J) :
    (transportFibreData h G).degreeBound = G.degreeBound := by
  subst K
  rfl

private theorem transport_generator {t : ℕ} {J K : Ideal (HolGerm (ComplexModel t))}
    (h : K = J) (G : ActualWeightedVertexGermData t J) (a : ActualVertexIndex t K) :
    (transportFibreData h G).generator a = G.generator (fibreVertexEquiv h a) := by
  subst K
  rfl

/- Elementary actual composition and private joint-coordinate readback;
no separate mathematical credit for these native helper restatements. -/
private theorem holomorphic_comp_zero {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G]
    (g : E → F) (hg : ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℂ g x) (hg0 : g 0 = 0)
    (f : F → G) (hf : ∀ᶠ y in 𝓝 (0 : F), DifferentiableAt ℂ f y) :
    ∀ᶠ x in 𝓝 (0 : E), DifferentiableAt ℂ (f ∘ g) x := by
  have ht : Tendsto g (𝓝 (0 : E)) (𝓝 (0 : F)) := by
    simpa only [hg0] using hg.self_of_nhds.continuousAt.tendsto
  filter_upwards [hg,ht.eventually hf] with x hx hfx
  exact hfx.comp x hx

private theorem jointPoint_base {n : ℕ} (p : CoordinateSpace n × ℂ) (i : Fin n) :
    jointPoint n p (i.castAdd 1) = p.1 i := by
  change (Fin.addCases (motive := fun _ : Fin (n+1) => CoordinateSpace n × ℂ →L[ℂ] ℂ)
    (fun j : Fin n => (ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.fst ℂ (CoordinateSpace n) ℂ))
    (fun _ : Fin 1 => ContinuousLinearMap.snd ℂ (CoordinateSpace n) ℂ) (i.castAdd 1)) p = p.1 i
  rw [Fin.addCases_left]
  rfl

private theorem jointPoint_parameter {n : ℕ} (p : CoordinateSpace n × ℂ) :
    jointPoint n p (parameterIndex n) = p.2 := by
  change (Fin.addCases (motive := fun _ : Fin (n+1) => CoordinateSpace n × ℂ →L[ℂ] ℂ)
    (fun j : Fin n => (ContinuousLinearMap.proj j).comp
      (ContinuousLinearMap.fst ℂ (CoordinateSpace n) ℂ))
    (fun _ : Fin 1 => ContinuousLinearMap.snd ℂ (CoordinateSpace n) ℂ) ((0 : Fin 1).natAdd n)) p = p.2
  rw [Fin.addCases_right]
  rfl


private def toModel (n : ℕ) : CoordinateSpace n →L[ℂ] ComplexModel n :=
  (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin n)).symm.toContinuousLinearMap

private def baseParameter (e t : ℕ) :
    CoordinateSpace (e+t) × ℂ →L[ℂ] ComplexModel e × ℂ :=
  ((tangentProjection e t).comp ((toModel (e+t)).comp
    (ContinuousLinearMap.fst ℂ (CoordinateSpace (e+t)) ℂ))).prod
      (ContinuousLinearMap.snd ℂ (CoordinateSpace (e+t)) ℂ)

private def baseCoordinates (d t : ℕ) : ComplexModel d →L[ℂ] CoordinateSpace (d+t) :=
  (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin (d+t))).toContinuousLinearMap.comp (tangentInclusion d t)

private def normalCoordinates (d e t : ℕ) :
    CoordinateSpace (e+t) × ℂ →L[ℂ] CoordinateSpace (d+t) :=
  (EuclideanSpace.equiv (𝕜 := ℂ) (ι := Fin (d+t))).toContinuousLinearMap.comp
    ((actualJointNormalInclusion d t).comp ((actualJointNormalProjection e t).comp
      ((toModel (e+t)).comp (ContinuousLinearMap.fst ℂ (CoordinateSpace (e+t)) ℂ))))

private def tailBaseChange (d e t : ℕ) (Φ : ComplexModel e × ℂ → ComplexModel d)
    (p : CoordinateSpace (e+t) × ℂ) : CoordinateSpace (d+t) × ℂ :=
  (baseCoordinates d t (Φ (baseParameter e t p)) + normalCoordinates d e t p,p.2)

private theorem tailBaseChange_zero (d e t : ℕ) (Φ : ComplexModel e × ℂ → ComplexModel d)
    (hΦ0 : Φ 0 = 0) : tailBaseChange d e t Φ 0 = 0 := by
  simp only [tailBaseChange,map_zero,hΦ0,zero_add,Prod.snd_zero]
  rfl

private theorem tailBaseChange_parameter (d e t : ℕ) (Φ : ComplexModel e × ℂ → ComplexModel d)
    (p : CoordinateSpace (e+t) × ℂ) : (tailBaseChange d e t Φ p).2 = p.2 := rfl

private theorem tailBaseChange_base (d e t : ℕ) (Φ : ComplexModel e × ℂ → ComplexModel d)
    (p : CoordinateSpace (e+t) × ℂ) (i : Fin d) :
    (tailBaseChange d e t Φ p).1 (i.castAdd t) = Φ (baseParameter e t p) i := by
  change tangentInclusion d t (Φ (baseParameter e t p)) (i.castAdd t) +
    actualJointNormalInclusion d t (actualJointNormalProjection e t (toModel (e+t) p.1)) (i.castAdd t) = _
  rw [tangentInclusion_tangent,actualJointNormalInclusion_tangent,add_zero]

private theorem tailBaseChange_normal (d e t : ℕ) (Φ : ComplexModel e × ℂ → ComplexModel d)
    (p : CoordinateSpace (e+t) × ℂ) (i : Fin t) :
    (tailBaseChange d e t Φ p).1 (i.natAdd d) = p.1 (i.natAdd e) := by
  change tangentInclusion d t (Φ (baseParameter e t p)) (i.natAdd d) +
    actualJointNormalInclusion d t (actualJointNormalProjection e t (toModel (e+t) p.1)) (i.natAdd d) = _
  rw [tangentInclusion_normal,actualJointNormalInclusion_normal,actualJointNormalProjection_apply,zero_add]
  rfl

private theorem tailBaseChange_holomorphic (d e t : ℕ) (Φ : ComplexModel e × ℂ → ComplexModel d)
    (hΦ : ∀ᶠ p in 𝓝 (0 : ComplexModel e × ℂ), DifferentiableAt ℂ Φ p) :
    ∀ᶠ p in 𝓝 (0 : CoordinateSpace (e+t) × ℂ), DifferentiableAt ℂ (tailBaseChange d e t Φ) p := by
  have hc := holomorphic_comp_zero (baseParameter e t)
    (Eventually.of_forall fun _ => (baseParameter e t).differentiableAt) (map_zero _) Φ hΦ
  filter_upwards [hc] with p hp
  exact (((baseCoordinates d t).differentiableAt.comp p hp).add
    (normalCoordinates d e t).differentiableAt).prodMk differentiableAt_snd

private def scaledPoint (d t L : ℕ) (w : Fin t → ℕ) (p : CoordinateSpace (d+t) × ℂ) :=
  actualWeightedScalingMap (extendedWeight d t L w) (jointPoint (d+t) p)

private theorem scaledPoint_zero (d t L : ℕ) (w : Fin t → ℕ) : scaledPoint d t L w 0 = 0 := by
  unfold scaledPoint
  rw [map_zero]
  ext i
  simp [actualWeightedScalingMap]

private theorem scaledPoint_holomorphic (d t L : ℕ) (w : Fin t → ℕ) :
    ∀ᶠ p in 𝓝 (0 : CoordinateSpace (d+t) × ℂ), DifferentiableAt ℂ (scaledPoint d t L w) p :=
  Eventually.of_forall fun p =>
    (differentiable_actualWeightedScalingMap (extendedWeight d t L w) _).comp p
      (jointPoint (d+t)).differentiableAt

private theorem scaledPoint_base (d t L : ℕ) (w : Fin t → ℕ)
    (p : CoordinateSpace (d+t) × ℂ) (i : Fin d) :
    scaledPoint d t L w p (i.castAdd t) = p.2 ^ L * p.1 (i.castAdd t) := by
  change jointPoint (d+t) p (parameterIndex (d+t)) ^ extendedWeight d t L w (i.castAdd t) *
    jointPoint (d+t) p ((i.castAdd t).castAdd 1) = _
  rw [jointPoint_parameter,jointPoint_base,extendedWeight_base]

private theorem scaledPoint_normal (d t L : ℕ) (w : Fin t → ℕ)
    (p : CoordinateSpace (d+t) × ℂ) (i : Fin t) :
    scaledPoint d t L w p (i.natAdd d) = p.2 ^ w i * p.1 (i.natAdd d) := by
  change jointPoint (d+t) p (parameterIndex (d+t)) ^ extendedWeight d t L w (i.natAdd d) *
    jointPoint (d+t) p ((i.natAdd d).castAdd 1) = _
  rw [jointPoint_parameter,jointPoint_base,extendedWeight_normal]

private theorem jointBaseMap_base (d e t : ℕ) (φ : ComplexModel e → ComplexModel d)
    (v : ComplexModel (e+t)) (i : Fin d) :
    jointBaseMap d e t φ v (i.castAdd t) = φ (tangentProjection e t v) i := by
  simp only [jointBaseMap,PiLp.add_apply,tangentInclusion_tangent,
    actualJointNormalInclusion_tangent,add_zero]

private theorem jointBaseMap_normal (d e t : ℕ) (φ : ComplexModel e → ComplexModel d)
    (v : ComplexModel (e+t)) (i : Fin t) : jointBaseMap d e t φ v (i.natAdd d) = v (i.natAdd e) := by
  simp only [jointBaseMap,PiLp.add_apply,tangentInclusion_normal,
    actualJointNormalInclusion_normal,actualJointNormalProjection_apply,zero_add]

private theorem scaled_base_change_commutes (d e t L : ℕ) (w : Fin t → ℕ)
    (φ : ComplexModel e → ComplexModel d) (Φ : ComplexModel e × ℂ → ComplexModel d)
    (p : CoordinateSpace (e+t) × ℂ)
    (h : φ ((baseParameter e t p).2 ^ L • (baseParameter e t p).1) =
      (baseParameter e t p).2 ^ L • Φ (baseParameter e t p)) :
    jointBaseMap d e t φ (scaledPoint e t L w p) =
      scaledPoint d t L w (tailBaseChange d e t Φ p) := by
  have hb : tangentProjection e t (scaledPoint e t L w p) = p.2 ^ L • (baseParameter e t p).1 := by
    ext i
    rw [tangentProjection_apply,scaledPoint_base]
    rfl
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [jointBaseMap_base,hb,scaledPoint_base,tailBaseChange_parameter,tailBaseChange_base]
    exact congrArg (fun v : ComplexModel d => v j) h
  · rw [jointBaseMap_normal,scaledPoint_normal,scaledPoint_normal,
      tailBaseChange_parameter,tailBaseChange_normal]

private theorem headMonomial_baseChange (d e t : ℕ) (Φ : ComplexModel e × ℂ → ComplexModel d)
    (p : CoordinateSpace (e+t) × ℂ) (γ : Fin t →₀ ℕ) :
    coordinateMonomial (actualJoinedExponent (0 : Fin d →₀ ℕ) γ) (tailBaseChange d e t Φ p).1 =
      coordinateMonomial (actualJoinedExponent (0 : Fin e →₀ ℕ) γ) p.1 := by
  simp [coordinateMonomial,Fin.prod_univ_add,actualJoinedExponent,tailBaseChange_normal]

/-- Actual arbitrary analytic base change produces SAME original lifts and whole fibre data. -/
theorem exists_same_base_changed_uniform_tails (d e t : ℕ)
    (I : Ideal (HolGerm (ComplexModel (d+t)))) (P : FibreLiftUniformTailData d t I)
    (φ : ComplexModel e → ComplexModel d)
    (hφ : ∀ᶠ v in 𝓝 (0 : ComplexModel e), DifferentiableAt ℂ φ v) (hφ0 : φ 0 = 0) :
    let IB := Ideal.map (jointBasePullback d e t φ hφ hφ0).toRingHom I
    let hJ := base_changed_fibre_ideal_eq d e t I φ hφ hφ0
    ∃ PB : FibreLiftUniformTailData e t IB,
      PB.fibre = transportFibreData hJ P.fibre ∧ PB.baseWeight = P.baseWeight ∧ PB.bound = P.bound ∧
      ∀ a, PB.lift a = jointBasePullback d e t φ hφ hφ0 (P.lift (fibreVertexEquiv hJ a)) := by
  let IB := Ideal.map (jointBasePullback d e t φ hφ hφ0).toRingHom I
  let hJ := base_changed_fibre_ideal_eq d e t I φ hφ hφ0
  let v := fibreVertexEquiv hJ
  have hv : ∀ a, (v a).val = a.val := fun a => fibreVertexEquiv_val hJ a
  let G := transportFibreData hJ P.fibre
  let F := fun a => jointBasePullback d e t φ hφ hφ0 (P.lift (v a))
  let L := P.baseWeight
  let w := degLexWeight t P.fibre.degreeBound
  have hDeg : G.degreeBound = P.fibre.degreeBound := transport_degree hJ P.fibre
  have hMember : ∀ a, F a ∈ IB ∧ jointBaseZeroTrace e t (F a) = G.generator a := by
    intro a
    constructor
    · exact Ideal.mem_map_of_mem _ (P.member_trace (v a)).1
    · exact (jointBaseZeroTrace_jointBasePullback d e t φ hφ hφ0 (P.lift (v a))).trans
        ((P.member_trace (v a)).2.trans (transport_generator hJ P.fibre a).symm)
  choose f hf hfEq using fun a => HolGerm.exists_eq_mk (F a)
  have hRep (a) : ∀ᶠ z in 𝓝 (0 : ComplexModel (e+t)),
      f a z = P.representative (v a) (jointBaseMap d e t φ z) := by
    have he := (hfEq a).symm.trans
      (congrArg (jointBasePullback d e t φ hφ hφ0) (P.representative_eq (v a)).symm)
    unfold jointBasePullback at he
    rw [compAlgHom_mk] at he
    exact HolGerm.mk_eq_mk_iff.mp he
  obtain ⟨Φ,rΦ,hrΦ,hΦon,hΦ0,hΦid⟩ := exists_holomorphic_base_rescaling d e L φ hφ hφ0 P.baseWeight_pos
  have hΦ : ∀ᶠ p in 𝓝 (0 : ComplexModel e × ℂ), DifferentiableAt ℂ Φ p := by
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self hrΦ)] with p hp
    exact hΦon.differentiableAt (isOpen_ball.mem_nhds hp)
  let ψ := tailBaseChange d e t Φ
  let A := fun a p => P.tailFactor (v a) (ψ p)
  have hparam : ∀ p, (ψ p).2 = p.2 := fun _ => rfl
  have hhead : ∀ p γ, coordinateMonomial (actualJoinedExponent (0 : Fin d →₀ ℕ) γ) (ψ p).1 =
      coordinateMonomial (actualJoinedExponent (0 : Fin e →₀ ℕ) γ) p.1 :=
    fun p γ => headMonomial_baseChange d e t Φ p γ
  have hψ := tailBaseChange_holomorphic d e t Φ hΦ
  have hψ0 : ψ 0 = 0 := tailBaseChange_zero d e t Φ hΦ0
  have hψt : Tendsto ψ (𝓝 (0 : CoordinateSpace (e+t) × ℂ))
      (𝓝 (0 : CoordinateSpace (d+t) × ℂ)) := by
    have ht : Tendsto ψ (𝓝 (0 : CoordinateSpace (e+t) × ℂ)) (𝓝 (ψ 0)) :=
      hψ.self_of_nhds.continuousAt.tendsto
    simpa only [hψ0] using ht
  have hOldOpen : IsOpen (ball (0 : CoordinateSpace (d+t)) P.radius ×ˢ ball (0 : ℂ) P.radius) :=
    isOpen_ball.prod isOpen_ball
  have hRange := hψt.eventually (hOldOpen.mem_nhds
    (show (0 : CoordinateSpace (d+t) × ℂ) ∈ ball 0 P.radius ×ˢ ball 0 P.radius from
      ⟨mem_ball_self P.radius_pos,mem_ball_self P.radius_pos⟩))
  have hA (a) : ∀ᶠ p in 𝓝 (0 : CoordinateSpace (e+t) × ℂ), DifferentiableAt ℂ (A a) p := by
    apply holomorphic_comp_zero ψ hψ hψ0 (P.tailFactor (v a))
    filter_upwards [hOldOpen.mem_nhds
      (show (0 : CoordinateSpace (d+t) × ℂ) ∈ ball 0 P.radius ×ˢ ball 0 P.radius from
        ⟨mem_ball_self P.radius_pos,mem_ball_self P.radius_pos⟩)] with p hp
    exact (P.factor_hol (v a)).differentiableAt (hOldOpen.mem_nhds hp)
  have hs0 := scaledPoint_zero e t L w
  have hs := scaledPoint_holomorphic e t L w
  have hScaled (a) : ∀ᶠ p in 𝓝 (0 : CoordinateSpace (e+t) × ℂ),
      DifferentiableAt ℂ (fun p => f a (scaledPoint e t L w p)) p :=
    holomorphic_comp_zero (scaledPoint e t L w) hs hs0 (f a) (hf a)
  have hst : Tendsto (scaledPoint e t L w) (𝓝 (0 : CoordinateSpace (e+t) × ℂ))
      (𝓝 (0 : ComplexModel (e+t))) := by
    simpa only [hs0] using hs.self_of_nhds.continuousAt.tendsto
  have hpret : Tendsto (baseParameter e t) (𝓝 (0 : CoordinateSpace (e+t) × ℂ))
      (𝓝 (0 : ComplexModel e × ℂ)) := by
    simpa only [map_zero] using (baseParameter e t).continuous.tendsto (0 : CoordinateSpace (e+t) × ℂ)
  have hSquare : ∀ᶠ p in 𝓝 (0 : CoordinateSpace (e+t) × ℂ),
      jointBaseMap d e t φ (scaledPoint e t L w p) = scaledPoint d t L w (ψ p) := by
    filter_upwards [hpret.eventually (isOpen_ball.mem_nhds (mem_ball_self hrΦ))] with p hp
    exact scaled_base_change_commutes d e t L w φ Φ p (hΦid _ hp)
  have hIdentity (a) : ∀ᶠ p in 𝓝 (0 : CoordinateSpace (e+t) × ℂ),
      f a (scaledPoint e t L w p) = p.2 ^ weightedDegree w a.val *
        (coordinateMonomial (actualJoinedExponent (0 : Fin e →₀ ℕ) a.val) p.1 + p.2 * A a p) := by
    filter_upwards [hst.eventually (hRep a),hSquare,hRange] with p hrep hsquare hrange
    calc
      _ = P.representative (v a) (jointBaseMap d e t φ (scaledPoint e t L w p)) := hrep
      _ = P.representative (v a) (scaledPoint d t L w (ψ p)) := congrArg (P.representative (v a)) hsquare
      _ = (ψ p).2 ^ weightedDegree w (v a).val *
          (coordinateMonomial (actualJoinedExponent (0 : Fin d →₀ ℕ) (v a).val) (ψ p).1 +
            (ψ p).2 * P.tailFactor (v a) (ψ p)) := P.weighted_identity (v a) (ψ p) hrange
      _ = _ := by
        rw [hv a,hparam p,hhead p]
  have hall : ∀ᶠ p in 𝓝 (0 : CoordinateSpace (e+t) × ℂ),
      ψ p ∈ ball (0 : CoordinateSpace (d+t)) P.radius ×ˢ ball (0 : ℂ) P.radius ∧
      ∀ a, DifferentiableAt ℂ (A a) p ∧ DifferentiableAt ℂ (fun p => f a (scaledPoint e t L w p)) p ∧
        f a (scaledPoint e t L w p) = p.2 ^ weightedDegree w a.val *
          (coordinateMonomial (actualJoinedExponent (0 : Fin e →₀ ℕ) a.val) p.1 + p.2 * A a p) :=
    hRange.and (eventually_all.mpr fun a => (hA a).and ((hScaled a).and (hIdentity a)))
  obtain ⟨R,hR,hAll⟩ := Metric.eventually_nhds_iff_ball.mp hall
  have hProd (p : CoordinateSpace (e+t) × ℂ)
      (hp : p ∈ ball (0 : CoordinateSpace (e+t)) R ×ˢ ball (0 : ℂ) R) : p ∈ ball 0 R := by
    rw [mem_ball_zero_iff,Prod.norm_mk]
    exact max_lt (mem_ball_zero_iff.mp hp.1) (mem_ball_zero_iff.mp hp.2)
  let PB : FibreLiftUniformTailData e t IB := {
    fibre := G
    lift := F
    member_trace := hMember
    baseWeight := L
    baseWeight_pos := P.baseWeight_pos
    head_lt := by
      intro a
      rw [hDeg]
      simpa only [hv a,L] using P.head_lt (v a)
    representative := f
    representative_hol := hf
    representative_eq := fun a => (hfEq a).symm
    tailFactor := A
    radius := R
    radius_pos := hR
    bound := P.bound
    bound_pos := P.bound_pos
    factor_hol := fun a p hp => ((hAll p (hProd p hp)).2 a).1.differentiableWithinAt
    scaled_hol := by
      intro a
      simpa only [hDeg,w,scaledPoint] using (show DifferentiableOn ℂ (fun p => f a (scaledPoint e t L w p))
        (ball (0 : CoordinateSpace (e+t)) R ×ˢ ball (0 : ℂ) R) from
          fun p hp => ((hAll p (hProd p hp)).2 a).2.1.differentiableWithinAt)
    factor_bound := fun a p hp => P.factor_bound (v a) (ψ p) (hAll p (hProd p hp)).1
    weighted_identity := by
      intro a p hp
      simpa only [hDeg,w,scaledPoint] using ((hAll p (hProd p hp)).2 a).2.2 }
  exact ⟨PB,rfl,rfl,rfl,fun _ => rfl⟩

end
end Hironaka.HironakaChowAnalyticBaseChangeUniformTails
