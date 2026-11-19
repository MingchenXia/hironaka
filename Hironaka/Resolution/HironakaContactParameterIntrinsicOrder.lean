import Hironaka.Resolution.HironakaSmoothSubmersionContactParameterCoefficientIdeals
import Hironaka.MarkedIdeal.CoefficientIdealAlongRestriction
set_option autoImplicit false
open Set Filter
open scoped Topology Manifold ContDiff
universe u v
namespace Hironaka.HironakaContactParameterIntrinsicOrder
open Hironaka.HolomorphicIdealSheaves Hironaka.RegularLocusDense Hironaka.BlowupSequences
  IdealOrderArithmetic BlowupTowers BlowupFlatCoordinates HadamardBridge OrderTaylor GermIdealOrder IdealWeightPowers
  RelativePrincipalizationSpan GermIdealPullbackCalculus DerivativeIdealAlongEtale
  MarkedIdeals MarkedIdeal CoefficientIdealRestriction CoefficientIdealAlongRestriction
  HomogenizedIdealAlong HironakaSmoothSubmersionContactParameterCharts
  HironakaSmoothSubmersionContactParameterCoefficientIdeals HironakaSmoothSubmersionTangentContact
  HironakaSmoothSubmersionRelativeOrder HironakaSmoothSubmersionRelativeGeometry
  TangentDirectionAlong GiraudAlong HironakaSmoothSubmersionCoefficientIdeals
noncomputable section
variable {n b : ℕ} {X : CMfd.{u} n} {Y : CMfd.{v} b}

/-- Ordinary local geometric retraction data imply every scalar threshold. -/
theorem scalar_order_iff_actual_local_retraction {σ : Y → X} {r : X → Y}
    {C : Set X} {z : Y}
    (hσ : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel n) σ w)
    (hr : ∀ᶠ x in 𝓝 (σ z), MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel b) r x)
    (hrz : r (σ z) = z) (hσC : ∀ w : Y, σ w ∈ C)
    (hround : ∀ᶠ x in 𝓝 (σ z), x ∈ C → σ (r x) = x) (g : X → ℂ) (q : ℕ) :
    VanishesToOrderOn n C (σ z) q g ↔ VanishesToOrderOn b univ z q (g ∘ σ) := by
  constructor
  · rintro ⟨h,hh,he⟩
    refine ⟨h ∘ σ,comp_mem_idealPow_pointIdeal hσ q hh,?_⟩
    filter_upwards [hσ.self_of_nhds.continuousAt.eventually he] with w hw _
    exact hw (hσC w)
  · intro hg
    have hp := mem_idealPow_of_vanishesToOrderOn_univ hg
    have hp' : (idealPow (pointIdeal b (r (σ z))) q).mem (r (σ z)) (g ∘ σ) := by
      simpa only [hrz] using hp
    refine ⟨(g ∘ σ) ∘ r,comp_mem_idealPow_pointIdeal hr q hp',?_⟩
    filter_upwards [hround] with x hx hxC
    simp only [Function.comp_apply,hx hxC]

theorem whole_orderGE_iff_actual_local_retraction {σ : Y → X} {r : X → Y}
    {C : Set X} {z : Y}
    (hσ : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel n) σ w)
    (hr : ∀ᶠ x in 𝓝 (σ z), MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel b) r x)
    (hrz : r (σ z) = z) (hσC : ∀ w : Y, σ w ∈ C)
    (hround : ∀ᶠ x in 𝓝 (σ z), x ∈ C → σ (r x) = x)
    (I : GermIdeal n X) (hI : ∀ g, I.mem (σ z) g → HolomorphicAt n g (σ z)) (q : ℕ) :
    OrderGE b univ (GermIdeal.pullback (m := b) σ I) z q ↔ OrderGE n C I (σ z) q := by
  have hiff := scalar_order_iff_actual_local_retraction hσ hr hrz hσC hround
  constructor
  · intro h g hg
    have hcomp : (GermIdeal.pullback (m := b) σ I).mem z (g ∘ σ) :=
      GermIdeal.mem_pullback_iff.mpr (InvertibleIdealQuotient.isInSpanAt_self
        ⟨g,hg,rfl⟩ (holomorphicAt_comp_map hσ (hI g hg)))
    exact (hiff g q).mpr (h _ hcomp)
  · intro h g hg
    refine IsInSpanAt.vanishesToOrderOn (GermIdeal.mem_pullback_iff.mp hg) ?_
    rintro _ ⟨a,ha,rfl⟩
    exact (hiff a q).mp (h a ha)

theorem whole_order_eq_actual_local_retraction {σ : Y → X} {r : X → Y}
    {C : Set X} {z : Y}
    (hσ : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel n) σ w)
    (hr : ∀ᶠ x in 𝓝 (σ z), MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel b) r x)
    (hrz : r (σ z) = z) (hσC : ∀ w : Y, σ w ∈ C)
    (hround : ∀ᶠ x in 𝓝 (σ z), x ∈ C → σ (r x) = x)
    (I : GermIdeal n X) (hI : ∀ g, I.mem (σ z) g → HolomorphicAt n g (σ z)) :
    order b univ (GermIdeal.pullback (m := b) σ I) z = order n C I (σ z) := by
  have he := whole_orderGE_iff_actual_local_retraction hσ hr hrz hσC hround I hI
  simp only [order,he]

theorem mem_cosupport_iff_actual_local_retraction {σ : Y → X} {r : X → Y}
    {C : Set X} {z : Y}
    (hσ : ∀ᶠ w in 𝓝 z, MDifferentiableAt 𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel n) σ w)
    (hr : ∀ᶠ x in 𝓝 (σ z), MDifferentiableAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel b) r x)
    (hrz : r (σ z) = z) (hσC : ∀ w : Y, σ w ∈ C)
    (hround : ∀ᶠ x in 𝓝 (σ z), x ∈ C → σ (r x) = x)
    (I : GermIdeal n X) (hI : ∀ g, I.mem (σ z) g → HolomorphicAt n g (σ z)) (d : ℕ) :
    z ∈ cosupport b univ (GermIdeal.pullback (m := b) σ I) d ↔ σ z ∈ cosupport n C I d := by
  have he := whole_orderGE_iff_actual_local_retraction hσ hr hrz hσC hround I hI d
  exact ⟨fun h => ⟨hσC z,he.mp h.2⟩,fun h => ⟨mem_univ z,he.mpr h.2⟩⟩

def actualParameterRetraction {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (b : ℕ) (z : parameterOpen Φ b) : X → parameterOpen Φ b :=
  openInv (parameterOpen Φ b) z ∘ (fun p => coordinateProjection n b (flatMap Φ p))

theorem actualProjection_contMDiffOn {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x)) (b : ℕ) :
    ContMDiffOn 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel b) ∞
      (fun p => coordinateProjection n b (flatMap Φ p)) (flatDomain Φ) := by
  intro p hp
  have hΦ : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ Φ.toFun
      (chartAt (ComplexModel n) x p) :=
    (contDiffAt_of_differentiableOn_complex Φ.toFun_holomorphic Φ.isOpen_source hp.2).contMDiffAt
  have hc : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (chartAt (ComplexModel n) x) p :=
    (contMDiffOn_chart (n := ∞)).contMDiffAt ((chartAt (ComplexModel n) x).open_source.mem_nhds hp.1)
  exact (((coordinateProjection n b).contDiff (n := ∞)).contDiffAt.contMDiffAt.comp
    p (hΦ.comp p hc)).contMDiffWithinAt

theorem actual_parameter_retraction_geometry {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hb : b ≤ n) (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (C : Set X) (hC : ∀ p ∈ flatDomain Φ, p ∈ C ↔ flatMap Φ p ∈ complexCoordinatePlane n b)
    (z : parameterOpen Φ b) :
    (∀ w : parameterOpen Φ b, parameterMapOn Φ b w ∈ C) ∧
    (∀ᶠ p in 𝓝 (parameterMapOn Φ b z), MDifferentiableAt
      𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel b) (actualParameterRetraction Φ b z) p) ∧
    actualParameterRetraction Φ b z (parameterMapOn Φ b z) = z ∧
    (∀ᶠ p in 𝓝 (parameterMapOn Φ b z), p ∈ C →
      parameterMapOn Φ b (actualParameterRetraction Φ b z p) = p) := by
  let R : X → ComplexModel b := fun p => coordinateProjection n b (flatMap Φ p)
  have hd := parameterMap_flat_dictionary Φ b hΦsrc z.val z.property
  have hround := parameterMap_roundtrip Φ b hb hΦsrc
  have hRz : R (parameterMapOn Φ b z) = z.val := hround.1 z.val z.property
  have hRdiff : ∀ᶠ p in 𝓝 (parameterMapOn Φ b z), MDifferentiableAt
      𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel b) R p := by
    filter_upwards [(isOpen_flatDomain Φ).mem_nhds hd.1] with p hp
    exact ((actualProjection_contMDiffOn Φ b).contMDiffAt
      ((isOpen_flatDomain Φ).mem_nhds hp)).mdifferentiableAt (by simp)
  have hInv : ∀ᶠ w in 𝓝 (R (parameterMapOn Φ b z)), MDifferentiableAt
      𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel b) (openInv (parameterOpen Φ b) z) w := by
    rw [hRz]
    exact (isLocalInverseAt_val (parameterOpen Φ b) z).mdiff_inv
  refine ⟨?_,?_,?_,?_⟩
  · intro w
    have hw := parameterMap_flat_dictionary Φ b hΦsrc w.val w.property
    apply (hC _ hw.1).mpr
    rw [hw.2]
    exact coordinateInclusion_mem_complexCoordinatePlane w.val
  · filter_upwards [hRdiff,hRdiff.self_of_nhds.continuousAt.eventually hInv] with p hp hi
    exact hi.comp p hp
  · change openInv (parameterOpen Φ b) z (R (parameterMapOn Φ b z)) = z
    rw [hRz]
    simp [openInv,z.property]
  · filter_upwards [(isOpen_flatDomain Φ).mem_nhds hd.1] with p hp hpC
    have hpr := hround.2 p hp ((hC p hp).mp hpC)
    change parameterMap Φ b (openInv (parameterOpen Φ b) z (R p)).val = p
    have hpR : R p ∈ parameterOpen Φ b := hpr.1
    simp only [openInv,dif_pos hpR]
    exact hpr.2

theorem actual_parameter_whole_orderGE {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hb : b ≤ n) (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (C : Set X) (hC : ∀ p ∈ flatDomain Φ, p ∈ C ↔ flatMap Φ p ∈ complexCoordinatePlane n b)
    (I : GermIdeal n X) (hI : I.IsCoherent) (z : parameterOpen Φ b) (q : ℕ) :
    OrderGE b univ (GermIdeal.pullback (m := b) (parameterMapOn Φ b) I) z q ↔
      OrderGE n C I (parameterMapOn Φ b z) q := by
  have hg := actual_parameter_retraction_geometry Φ hb hΦsrc C hC z
  have hσ : ∀ᶠ w in 𝓝 z, MDifferentiableAt
      𝓘(ℂ, ComplexModel b) 𝓘(ℂ, ComplexModel n) (parameterMapOn Φ b) w :=
    Eventually.of_forall fun w => (parameterMapOn_contMDiff Φ b hΦsrc w).mdifferentiableAt (by simp)
  exact whole_orderGE_iff_actual_local_retraction
    (Y := CMfd.of (n := b) (parameterOpen Φ b)) hσ hg.2.1 hg.2.2.1 hg.1 hg.2.2.2 I
    (fun g h => GermIdeal.IsCoherent.holomorphicAt_mem hI h) q

theorem actual_parameter_extended_order {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hb : b ≤ n) (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (C : Set X) (hC : ∀ p ∈ flatDomain Φ, p ∈ C ↔ flatMap Φ p ∈ complexCoordinatePlane n b)
    (I : GermIdeal n X) (hI : I.IsCoherent) (z : parameterOpen Φ b) :
    order b univ (GermIdeal.pullback (m := b) (parameterMapOn Φ b) I) z =
      order n C I (parameterMapOn Φ b z) := by
  have he := actual_parameter_whole_orderGE Φ hb hΦsrc C hC I hI z
  simp only [order,he]

theorem actual_parameter_cosupport {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hb : b ≤ n) (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (C : Set X) (hC : ∀ p ∈ flatDomain Φ, p ∈ C ↔ flatMap Φ p ∈ complexCoordinatePlane n b)
    (I : GermIdeal n X) (hI : I.IsCoherent) (d : ℕ) :
    cosupport b univ (GermIdeal.pullback (m := b) (parameterMapOn Φ b) I) d =
      parameterMapOn Φ b ⁻¹' cosupport n C I d := by
  ext z
  have hmem := (actual_parameter_retraction_geometry Φ hb hΦsrc C hC z).1 z
  exact ⟨fun hz => ⟨hmem,(actual_parameter_whole_orderGE Φ hb hΦsrc C hC I hI z d).mp hz.2⟩,
    fun hz => ⟨mem_univ z,(actual_parameter_whole_orderGE Φ hb hΦsrc C hC I hI z d).mpr hz.2⟩⟩

theorem intrinsicCoefficient_cosupp_eq_original {x : X}
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) x x))
    (hb : b ≤ n) (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) x).target)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N)
    (hd : 1 ≤ M.d) (C : Set X) (hCN : C ⊆ M.N)
    (hC : ∀ p ∈ flatDomain Φ, p ∈ C ↔ flatMap Φ p ∈ complexCoordinatePlane n b) :
    (intrinsicCoefficient (b := b) M (parameterMapOn Φ b)).cosupp =
      parameterMapOn Φ b ⁻¹' M.cosupp := by
  have hcoeff := isCoherent_coeffMarkedAlong hI hN
  have hred := cosupp_coeffMarkedAlong_withN hN.2
    (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hI hg) hd hCN
  have hparam := actual_parameter_cosupport Φ hb hΦsrc C hC
    (coeffMarkedAlong M).ideal hcoeff (coeffMarkedAlong M).d
  change cosupport b univ (GermIdeal.pullback (m := b) (parameterMapOn Φ b)
    (coeffMarkedAlong M).ideal) (coeffMarkedAlong M).d = _
  rw [hparam]
  have hred' : cosupport n C (coeffMarkedAlong M).ideal (coeffMarkedAlong M).d = M.cosupp ∩ C := hred
  rw [hred']
  ext z
  have hz := (actual_parameter_retraction_geometry Φ hb hΦsrc C hC z).1 z
  exact ⟨fun h => h.1,fun h => ⟨h,hz⟩⟩

/-- An internally produced result; never a caller input. -/
private def JointOriginalCosupport {m : ℕ} {Y₀ : CMfd.{u} m}
    (M : MarkedIdeal n X) (f : Y₀ → X) (U : Set X) (u : X → ℂ) (y : Y₀) : Prop :=
  ∃ (k t : ℕ)
    (Φ : LocalHolomorphicEquivAt (n := n) (chartAt (ComplexModel n) (f y) (f y)))
    (Γ : LocalHolomorphicEquivAt (n := m) (chartAt (ComplexModel m) y y)),
    m = n+t ∧ 0 < k ∧ k ≤ n ∧
    Φ.source ⊆ (chartAt (ComplexModel n) (f y)).target ∧
    Γ.source ⊆ (chartAt (ComplexModel m) y).target ∧
    (∀ z ∈ flatDomain Φ, z ∈ contactCarrier M.N U u ↔
      flatMap Φ z ∈ complexCoordinatePlane n (k-1)) ∧
    (∀ z ∈ flatDomain Γ, f z ∈ contactCarrier M.N U u ↔
      flatMap Γ z ∈ complexCoordinatePlane m ((k-1)+t)) ∧
    0 ∈ parameterOpen Φ (k-1) ∧ 0 ∈ parameterOpen Γ ((k-1)+t) ∧
    parameterMap Φ (k-1) 0 = f y ∧ parameterMap Γ ((k-1)+t) 0 = y ∧
    (intrinsicCoefficient (b := k-1) M (parameterMapOn Φ (k-1))).cosupp =
      parameterMapOn Φ (k-1) ⁻¹' M.cosupp ∧
    (intrinsicCoefficient (b := (k-1)+t) (markedPullback (m := m) f M)
      (parameterMapOn Γ ((k-1)+t))).cosupp =
      parameterMapOn Γ ((k-1)+t) ⁻¹' (markedPullback (m := m) f M).cosupp ∧
    ∃ hMaps : MapsTo (HironakaSmoothSubmersionRelativeDifferentialIdeals.actualTargetProjectionLinear (k-1) t)
        (parameterOpen Γ ((k-1)+t)) (parameterOpen Φ (k-1)),
    Manifold.IsSubmersionOfComplement (ComplexModel t)
      𝓘(ℂ, ComplexModel ((k-1)+t)) 𝓘(ℂ, ComplexModel (k-1)) ∞
      (restrictedOpenMap (X := CMfd.of (n := k-1) (ComplexModel (k-1)))
        (Y := CMfd.of (n := (k-1)+t) (ComplexModel ((k-1)+t)))
        (f := HironakaSmoothSubmersionRelativeDifferentialIdeals.actualTargetProjectionLinear (k-1) t)
        (parameterOpen Γ ((k-1)+t)) (parameterOpen Φ (k-1)) hMaps)

theorem exists_original_only_joint_intrinsic_cosupport {m : ℕ} {Y₀ : CMfd.{u} m} {f : Y₀ → X}
    (hf : Manifold.IsSubmersion 𝓘(ℂ, ComplexModel m) 𝓘(ℂ, ComplexModel n) ∞ f)
    (M : MarkedIdeal n X) (hI : M.ideal.IsCoherent) (hN : IsClosedSubmanifold n M.N)
    (hd : 1 ≤ M.d) (y : Y₀) (hy : y ∈ (markedPullback (m := m) f M).cosupp)
    (hmax : ¬ OrderGE n M.N M.ideal (f y) (M.d+1)) :
    ∃ (U : TopologicalSpace.Opens X) (u : X → ℂ), f y ∈ U ∧
      IsTangentDirectionAlong M.N M.ideal M.d (U : Set X) u ∧
      IsTangentDirectionAlong (f ⁻¹' M.N) (GermIdeal.pullback (m := m) f M.ideal)
        M.d (f ⁻¹' (U : Set X)) (u ∘ f) ∧
      JointOriginalCosupport M f (U : Set X) u y := by
  obtain ⟨U,u,hyU,hu,hup,hjoint⟩ := exists_original_only_joint_contact_parameters hf M hI hN hd y hy hmax
  obtain ⟨k,t,Φ,Γ,hmt,hk,hkn,hΦsrc,hΓsrc,_hΦ0,_hΓ0,_hΦU,hΦflag,hΓflag,
    hW0,hV0,hτ0,hσ0,_hτOn,_hσOn,_hτC,_hτRound,_hσC,_hσRound,hMaps,_hSquare,hP⟩ := hjoint
  have hCΦ : ∀ z ∈ flatDomain Φ, z ∈ contactCarrier M.N (U : Set X) u ↔
      flatMap Φ z ∈ complexCoordinatePlane n (k-1) := fun z hz => (hΦflag z hz).2
  have hCΓ : ∀ z ∈ flatDomain Γ, z ∈ f ⁻¹' contactCarrier M.N (U : Set X) u ↔
      flatMap Γ z ∈ complexCoordinatePlane m ((k-1)+t) := fun z hz => (hΓflag z hz).2.2
  have htgt := intrinsicCoefficient_cosupp_eq_original Φ (by omega) hΦsrc M hI hN hd
    (contactCarrier M.N (U : Set X) u) (fun _ hz => hz.1.1) hCΦ
  have hsI : (markedPullback (m := m) f M).ideal.IsCoherent := isCoherent_pullback hf.contMDiff hI
  have hsN : IsClosedSubmanifold m (markedPullback (m := m) f M).N :=
    isClosedSubmanifold_preimage_submersion hf hN
  have hsrc := intrinsicCoefficient_cosupp_eq_original (X := Y₀) Γ (by omega) hΓsrc
    (markedPullback (m := m) f M) hsI hsN hd
    (f ⁻¹' contactCarrier M.N (U : Set X) u) (fun _ hz => hz.1.1) hCΓ
  exact ⟨U,u,hyU,hu,hup,k,t,Φ,Γ,hmt,hk,hkn,hΦsrc,hΓsrc,hCΦ,hCΓ,hW0,hV0,hτ0,hσ0,htgt,hsrc,hMaps,hP⟩

end
end Hironaka.HironakaContactParameterIntrinsicOrder
