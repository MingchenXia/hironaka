import Hironaka.Resolution.HironakaG1ProperCarrierNormalDerivativeTrace
import Hironaka.Resolution.HironakaActualWeightedNormalContact
import Hironaka.Resolution.HironakaG8ContactMax

/-! Genuine normal geometry on the ACTUAL proper cylinder, with full E.
The vertical field preserves every pulled base subset simultaneously.
No support-gap, raw-value or canonical-padding comparison is asserted.
Blueprint FIRST: hironaka-g1-proper-carrier-normal-contact.tex. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1ProperCarrierNormalContact
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  RelativePrincipalizationSpan GermIdealPullbackCalculus InvertibleIdealQuotient
  DerivativeIdeal DerivativeIdealAlong DerivativeIdealAlongEtale TangentDirectionAlong
  HironakaActualCoherentWeightedCoefficientMarked HironakaActualWeightedNormalPadding
  HironakaActualWeightedNormalAmbientDerivatives HironakaActualWeightedNormalContact
  HironakaActualOpenZeroSectionDifferentials HironakaActualRelativeNormalGeometry
  HironakaActualCentreJointJets HironakaActualIntrinsicStableAmbientIso
  HironakaActualZeroCoordinateContactSeed HironakaActualGraphContactCoefficient
  HironakaRelativeNormalIdeal HironakaActualSectionBoundaryGeometry
  HironakaSmoothSubmersionRelativeGeometry HironakaSmoothSubmersionRelativeOrder
  HironakaG1ProperCarrierNormalDerivativeTrace HironakaG8ContactMax
  HomogenizedIdealAlong MarkedIdeals MarkedIdeals.MarkedIdeal BlowupTowers
  ResolutionInvariantSpec GermIdealOrder IdealWeightPowers IdealOrderArithmetic
  RestrictedIdealExtension BlowupDerivativeIdeal CoefficientIdeal CompanionReduction

private def normalVector (n : ℕ) : ComplexModel (n+1) :=
  actualJointNormalInclusion n 1 (EuclideanSpace.single 0 1)

private theorem global_normal_derivative_one (n : ℕ) (x : ComplexModel (n+1)) :
    chartDeriv (complexChartAt x) (normalVector n) (addedCoordinate n)=fun _ => 1 := by
  funext y
  have h := graphFunction_chartDeriv_eq_one (zeroFunction n) y
    (differentiableAt_const _) (0 : Fin 1)
  simpa only [normalVector,addedCoordinate,complexChartAt,chartAt_self_eq] using h

private theorem global_normal_hol (n : ℕ) (x : ComplexModel (n+1)) :
    HolomorphicAt (n+1) (addedCoordinate n) x := by
  exact ((zero_coordinate_tangent (univ : Set (ComplexModel n))).mem x (mem_univ x)).1

private theorem global_vertical_tangent (n : ℕ) (S : Set (ComplexModel n))
    (x : ComplexModel (n+1)) :
    IsTangentField (tangentProjection n 1 ⁻¹' S) (complexChartAt x)
      (fun i _ => normalVector n i) x := by
  refine ⟨mem_complexChartAt_source x,fun _ => holomorphicAt_const _,fun g hg => ?_⟩
  refine ⟨holomorphicAt_fieldDeriv (mem_complexChartAt_source x)
    (fun _ => holomorphicAt_const _) hg.1,?_⟩
  filter_upwards [hg.1.eventually_nhds,hg.2.eventually_nhds] with y hgy hy hyS
  let γ : ℂ → ComplexModel (n+1) := fun a => y+a • normalVector n
  have hγ : HasDerivAt γ (normalVector n) 0 := by
    simpa only [γ,id_eq,one_smul] using
      (hasDerivAt_const_add_iff y).mpr ((hasDerivAt_id (0 : ℂ)).smul_const (normalVector n))
  have ht : Tendsto γ (𝓝 0) (𝓝 y) := by
    simpa only [γ,zero_smul,add_zero] using hγ.continuousAt.tendsto
  have heq : (g ∘ γ)=ᶠ[𝓝 (0 : ℂ)] (fun _ => 0) := by
    filter_upwards [ht.eventually hy] with a ha
    apply ha
    change tangentProjection n 1 (y+a • normalVector n)∈S
    simpa only [map_add,map_smul,normalVector,tangentProjection_actualJointNormalInclusion,
      smul_zero,add_zero] using (show tangentProjection n 1 y∈S from hyS)
  have hgd : DifferentiableAt ℂ g y := by
    rw [←mdifferentiableAt_iff_differentiableAt]
    exact hgy.self_of_nhds
  have hd : HasDerivAt (g ∘ γ) (fderiv ℂ g y (normalVector n)) 0 :=
    hgd.hasFDerivAt.comp_hasDerivAt_of_eq 0 hγ (by simp [γ])
  have hz : HasDerivAt (g ∘ γ) 0 0 := (hasDerivAt_const (0 : ℂ) (0 : ℂ)).congr_of_eventuallyEq heq
  have hval := hd.unique hz
  simpa [fieldDeriv_const,chartDeriv,complexChartAt,chartAt_self_eq] using hval

private theorem cylinder_preimage_image {n : ℕ} (U : Opens (ComplexModel n)) (S : Set U) :
    (Subtype.val : productOpen U → ComplexModel (n+1)) ⁻¹'
      (tangentProjection n 1 ⁻¹' ((Subtype.val : U → ComplexModel n) '' S))=
      projection U ⁻¹' S := by
  ext z
  constructor
  · rintro ⟨y,hy,he⟩
    change projection U z∈S
    exact (Subtype.ext he : y=projection U z) ▸ hy
  · intro hz
    exact ⟨projection U z,hz,rfl⟩

/-- ONE actual field, independent of S, preserves every pulled whole
vanishing ideal and differentiates the literal normal coordinate to one. -/
theorem exists_normal_tangent_field {n : ℕ} (U : Opens (ComplexModel n))
    (x : productOpen U) :
    ∃(e : ComplexChart (n+1) (productOpen U))(ξ : Fin (n+1) → productOpen U → ℂ),
      fieldDeriv e ξ (relativeNormalCoordinate U) x=1 ∧
      ∀S : Set U,IsTangentField (projection U ⁻¹' S) e ξ x := by
  let e := complexChartAt (n := n+1) x
  let ξ := transferField (Subtype.val : productOpen U → ComplexModel (n+1))
    (openInv (productOpen U) x) (complexChartAt x.val) e (fun i _ => normalVector n i)
  have hloc := isLocalInverseAt_val (n := n+1) (productOpen U) x
  have hx : x∈e.val.source := mem_complexChartAt_source x
  refine ⟨e,ξ,?_,?_⟩
  · have hnormal : HolomorphicAt (n+1) (relativeNormalCoordinate U) x :=
      Eventually.of_forall (normalCoordinate_mdifferentiable U)
    have htr := fieldDeriv_transfer hloc hx (mem_complexChartAt_source x.val)
      (fun i _ => normalVector n i) hnormal
    change fieldDeriv e ξ (relativeNormalCoordinate U) x=1
    rw [htr.self_of_nhds]
    have heq : (relativeNormalCoordinate U ∘ openInv (productOpen U) x)=ᶠ[𝓝 x.val]
        addedCoordinate n := by
      filter_upwards [(productOpen U).isOpen.mem_nhds x.property] with y hy
      change relativeNormalCoordinate U (openInv (productOpen U) x y)=addedCoordinate n y
      have hy' : y∈productOpen U := hy
      rw [openInv,dif_pos hy']
      rfl
    change fieldDeriv (complexChartAt x.val) (fun i _ => normalVector n i)
      (relativeNormalCoordinate U ∘ openInv (productOpen U) x) x.val=1
    rw [(fieldDeriv_congr (mem_complexChartAt_source x.val) heq).self_of_nhds,
      fieldDeriv_const,global_normal_derivative_one]
  · intro S
    have hfield := isTangentField_transfer hloc hx
      (global_vertical_tangent n ((Subtype.val : U → ComplexModel n) '' S) x.val)
    rw [cylinder_preimage_image U S] at hfield
    exact hfield

private def globalNormalPower (n d : ℕ) : GermIdeal (n+1) (ComplexModel (n+1)) :=
  finiteFunctionIdeal (fun _ : Unit => fun z => addedCoordinate n z^d)

private theorem global_normal_power_hol (n d : ℕ) (x : ComplexModel (n+1)) :
    HolomorphicAt (n+1) (fun z => addedCoordinate n z^d) x :=
  holomorphicAt_pow (global_normal_hol n x) d

private theorem global_normal_power_step (n : ℕ) (S : Set (ComplexModel n)) (r : ℕ) :
    (globalNormalPower n r).Le
      (derivIdealAlong (tangentProjection n 1 ⁻¹' S) (globalNormalPower n (r+1))) := by
  intro x g hg
  refine IsInSpanAt.trans ?_ hg
  rintro _ ⟨_i,rfl⟩
  let e : ComplexChart (n+1) (ComplexModel (n+1)) := complexChartAt x
  let ξ : Fin (n+1) → ComplexModel (n+1) → ℂ := fun i _ => normalVector n i
  have hp : (globalNormalPower n (r+1)).mem x (fun z => addedCoordinate n z^(r+1)) :=
    isInSpanAt_self ⟨(),rfl⟩ (global_normal_power_hol n (r+1) x)
  have hgen : DerivGenAlong (tangentProjection n 1 ⁻¹' S) (globalNormalPower n (r+1)) x
      (fieldDeriv e ξ (fun z => addedCoordinate n z^(r+1))) :=
    Or.inr (Or.inr ⟨e,ξ,_,global_vertical_tangent n S x,hp,rfl⟩)
  have hpow := chartDeriv_pow (v := normalVector n) (mem_complexChartAt_source x)
    (global_normal_hol n x) r
  have hcoef : (r : ℂ)+1≠0 := by exact_mod_cast (Nat.succ_ne_zero r)
  have he : (fun z => ((r : ℂ)+1)⁻¹ * fieldDeriv e ξ
      (fun y => addedCoordinate n y^(r+1)) z)=ᶠ[𝓝 x]
      (fun z => addedCoordinate n z^r) := by
    filter_upwards [hpow] with z hz
    rw [fieldDeriv_const,hz,global_normal_derivative_one]
    simp only [mul_one]
    rw [←mul_assoc,inv_mul_cancel₀ hcoef,one_mul]
  exact isInSpanAt_of_eq_mul hgen (global_normal_power_hol n r x)
    (holomorphicAt_const (((r : ℂ)+1)⁻¹)) he.symm

private theorem global_normal_power_iterate (n : ℕ) (S : Set (ComplexModel n)) :
    ∀j r,(globalNormalPower n r).Le
      (iterDerivIdealAlong (tangentProjection n 1 ⁻¹' S) (globalNormalPower n (r+j)) j)
  | 0,r => fun _ _ hg => hg
  | j+1,r => by
    have hm := derivIdealAlong_mono (N := tangentProjection n 1 ⁻¹' S)
      (global_normal_power_iterate n S j (r+1))
    intro x g hg
    have h := hm x g (global_normal_power_step n S r x g hg)
    have he : r+1+j=r+(j+1) := by omega
    simpa only [he,iterDerivIdealAlong] using h

private theorem normal_power_member_of_inclusion {n : ℕ} (U : Opens (ComplexModel n)) (N : Set U)
    (J : GermIdeal (n+1) (productOpen U)) (r j : ℕ) (x : productOpen U)
    (hinc : (GermIdeal.pullback (m := n+1)
      (Subtype.val : productOpen U → ComplexModel (n+1)) (globalNormalPower n (r+j))).Le J) :
    (iterDerivIdealAlong (projection U ⁻¹' N) J j).mem x
      (fun z => relativeNormalCoordinate U z^r) := by
  let S := (Subtype.val : U → ComplexModel n) '' N
  have hglob := global_normal_power_iterate n S j r x.val _
    (isInSpanAt_self ⟨(),rfl⟩ (global_normal_power_hol n r x.val))
  have hp : (GermIdeal.pullback (m := n+1)
      (Subtype.val : productOpen U → ComplexModel (n+1))
      (iterDerivIdealAlong (tangentProjection n 1 ⁻¹' S) (globalNormalPower n (r+j)) j)).mem x
      (fun z => relativeNormalCoordinate U z^r) :=
    GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self
      ⟨fun z => addedCoordinate n z^r,hglob,rfl⟩
      (Eventually.of_forall ((normalCoordinate_mdifferentiable U).pow r)))
  have hhol : ∀z g,(globalNormalPower n (r+j)).mem z g → HolomorphicAt (n+1) g z :=
    fun _ _ hg => hg.1
  rw [pullback_val_iterDerivIdealAlong (productOpen U) hhol j,
    cylinder_preimage_image U N] at hp
  have hmono : ∀l,(iterDerivIdealAlong (projection U ⁻¹' N)
      (GermIdeal.pullback (m := n+1) (Subtype.val : productOpen U → ComplexModel (n+1))
        (globalNormalPower n (r+j))) l).Le
      (iterDerivIdealAlong (projection U ⁻¹' N) J l) := by
    intro l
    induction l with
    | zero => exact hinc
    | succ l ih => exact derivIdealAlong_mono ih
  exact hmono j x _ hp

/-- Genuine relative normal-power membership on the WHOLE proper cylinder. -/
theorem normal_power_relative_member {n : ℕ} (U : Opens (ComplexModel n)) (N : Set U)
    (I : GermIdeal n U) (r j : ℕ) (x : productOpen U) :
    (iterDerivIdealAlong (projection U ⁻¹' N) (normalPaddingIdeal I (r+j)) j).mem x
      (fun z => relativeNormalCoordinate U z^r) := by
  apply normal_power_member_of_inclusion U N _ r j x
  rw [globalNormalPower,finiteFunctionIdeal_pullback _
    (fun _ => fun z => (global_normal_power_hol n (r+j) z).self_of_nhds)
    (Subtype.val : productOpen U → ComplexModel (n+1)) contMDiff_subtype_val]
  exact le_sumIdeal_right (isCoherent_finiteFunctionIdeal _
    (fun _ => (normalCoordinate_mdifferentiable U).pow (r+j)))

/-- The normal power in a coherent ideal supplies every lower normal
power in its relative derivative iterates on a cylinder. -/
theorem iterDerivIdealAlong_normal_power_mem {n : ℕ} (U : Opens (ComplexModel n))
    (N : Set U) (J : GermIdeal (n + 1) (productOpen U)) (hJ : J.IsCoherent) (r j : ℕ)
    (hpow : ∀ x, J.mem x (fun z => relativeNormalCoordinate U z ^ (r + j))) (x : productOpen U) :
    (iterDerivIdealAlong (projection U ⁻¹' N) J j).mem x
      (fun z => relativeNormalCoordinate U z ^ r) := by
  apply normal_power_member_of_inclusion U N J r j x
  rw [globalNormalPower, finiteFunctionIdeal_pullback _
    (fun _ => fun z => (global_normal_power_hol n (r + j) z).self_of_nhds)
    (Subtype.val : productOpen U → ComplexModel (n + 1)) contMDiff_subtype_val]
  intro y g hg
  apply GermIdealTotalTransform.mem_of_isInSpanAt_mem hJ
  exact hg.mono (by rintro _ ⟨_i, rfl⟩; exact hpow y)

/-- An actual whole normal-power member supplies normal contact with any
coherent whole ideal along the proper cylinder; no tangent packet is assumed. -/
theorem normal_tangent_of_power_member {n : ℕ} (U : Opens (ComplexModel n)) (N : Set U)
    (J : GermIdeal (n+1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ) (hd : 0 < d)
    (hpow : ∀x,(J.mem x (fun z => relativeNormalCoordinate U z^d))) :
    IsTangentDirectionAlong (projection U ⁻¹' N) J d univ (relativeNormalCoordinate U) := by
  refine ⟨isOpen_univ,?_,?_⟩
  · intro x _
    have he : 1 + (d - 1) = d := by omega
    simpa only [pow_one] using iterDerivIdealAlong_normal_power_mem U N J hJ 1 (d - 1)
      (by simpa only [he] using hpow) x
  · intro x _ _
    obtain ⟨e,ξ,hOne,hAll⟩ := exists_normal_tangent_field U x
    exact ⟨e,ξ,hAll N,by rw [hOne];exact one_ne_zero⟩

private theorem padding_coherent {n : ℕ} {U : Opens (ComplexModel n)}
    {I : GermIdeal n U} (hI : I.IsCoherent) (d : ℕ) :
    (normalPaddingIdeal I d).IsCoherent :=
  isCoherent_sumIdeal (isCoherent_pullback (projection_contMDiff U) hI)
    (isCoherent_finiteFunctionIdeal _ (fun _ => (normalCoordinate_mdifferentiable U).pow d))

/-- Coefficient formation retains the whole normal power at its new mark. -/
theorem coeffMarkedAlong_normal_power_mem {n : ℕ} {U : Opens (ComplexModel n)}
    (B : MarkedIdeal (n + 1) (productOpen U)) (hd : 0 < B.d)
    (hp : ∀ x, B.ideal.mem x (fun z => relativeNormalCoordinate U z ^ B.d)) (x : productOpen U) :
    (coeffMarkedAlong B).ideal.mem x (fun z => relativeNormalCoordinate U z ^ (coeffMarkedAlong B).d) := by
  let e := sumExp (fun j => B.d - j) B.d 0
  have hMark : (coeffMarkedAlong B).d = B.d * e := by
    change (Finset.range B.d).prod (fun j => B.d - j) = B.d * e
    simpa only [Nat.sub_zero] using (mul_sumExp (fun j => B.d - j) hd (i := 0)).symm
  have hNormal : HolomorphicAt (n + 1) (relativeNormalCoordinate U) x :=
    Eventually.of_forall (normalCoordinate_mdifferentiable U)
  have hPow := HomogenizedIdeal.pow_mem_idealPow (hp x) (holomorphicAt_pow_of hNormal B.d) e
  change IsInSpanAt (n := n + 1) (fun f => ∃ i, i < B.d ∧
    (idealPow (iterDerivIdealAlong B.N B.ideal i) (sumExp (fun j => B.d - j) B.d i)).mem x f) x _
  refine isInSpanAt_self ⟨0, hd, ?_⟩ (holomorphicAt_pow_of hNormal _)
  change (idealPow B.ideal e).mem x
    (fun z => relativeNormalCoordinate U z ^ (coeffMarkedAlong B).d)
  rw [hMark]
  simpa only [← pow_mul] using hPow

/-- The whole normal power bounds the relative order on a cylinder. -/
theorem normal_power_maximalOrder {n : ℕ} (U : Opens (ComplexModel n)) (N : Set U)
    (J : GermIdeal (n + 1) (productOpen U)) (hJ : J.IsCoherent) (d : ℕ)
    (hpow : ∀ x, J.mem x (fun z => relativeNormalCoordinate U z ^ d)) :
    IsMaximalOrderAlong (projection U ⁻¹' N) J d := by
  intro x hx
  have hHol : ∀ y g, J.mem y g → HolomorphicAt (n + 1) g y :=
    fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hJ hg
  have hOne : (iterDerivIdealAlong (projection U ⁻¹' N) J d).mem x (fun _ => 1) := by
    simpa only [zero_add, pow_zero] using iterDerivIdealAlong_normal_power_mem U N J hJ 0 d
      (by simpa only [zero_add] using hpow) x
  have hCos := cosupport_add_subset_cosupport_iterDerivIdealAlong hHol 1 d
    (by simpa only [Nat.add_comm] using hx)
  exact one_ne_zero ((vanishesToOrderOn_one_iff hCos.1 (holomorphicAt_const (1 : ℂ))).mp
    (hCos.2 _ hOne))

/-- Genuine normal tangent direction at the ORIGINAL native mark on the
actual proper cylinder, with no assumption about the old boundary. -/
theorem properNormalMarked_tangent {n : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hd : 0 < Q.d) :
    IsTangentDirectionAlong (properNormalMarked Q).N (properNormalMarked Q).ideal Q.d univ
      (relativeNormalCoordinate U) := by
  refine ⟨isOpen_univ,?_,?_⟩
  · intro x _
    have h := normal_power_relative_member U Q.N Q.ideal 1 (Q.d-1) x
    have he : 1+(Q.d-1)=Q.d := by omega
    simpa only [properNormalMarked,he,pow_one] using h
  · intro x _ _
    obtain ⟨e,ξ,hOne,hAll⟩ := exists_normal_tangent_field U x
    exact ⟨e,ξ,hAll Q.N,by rw [hOne];exact one_ne_zero⟩

/-- The literal z^d generator bounds the ACTUAL relative order everywhere,
including proper carriers; no maximal-order assumption on Q is used. -/
theorem properNormalMarked_maximalOrder {n : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hI : Q.ideal.IsCoherent) :
    IsMaximalOrderAlong (properNormalMarked Q).N (properNormalMarked Q).ideal Q.d := by
  refine normal_power_maximalOrder U Q.N _ (padding_coherent hI Q.d) Q.d fun x => ?_
  simpa only [Nat.add_zero, iterDerivIdealAlong] using normal_power_relative_member U Q.N Q.ideal Q.d 0 x

/-- Ordinary ORIGINAL native data supply the whole actual padded domain;
the proper cylinder, full E, positive mark and genuine nonzero are retained. -/
theorem properNormalMarked_isInvDomain {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    IsInvDomain (k+1) (properNormalMarked Q) := by
  have hD := isInvDomain_markedPullback_submersion (X := CMfd.of (n := n) U)
    (Y := CMfd.of (n := n+1) (productOpen U)) (projection_isSubmersion (U := U)) Q hQ
  have he : k+((n+1)-n)=k+1 := by omega
  rw [he] at hD
  refine ⟨⟨hD.isWellFormed.isClosedSubmanifold_N,padding_coherent hQ.isWellFormed.isCoherent Q.d,
    hD.isWellFormed.isSNCDivisor,hD.isWellFormed.isTransverse⟩,
    hD.dimLE,hD.one_le_d,?_⟩
  intro z hz
  obtain ⟨g,hg,hfreq⟩ := hD.isNonzeroAlongAt z hz
  exact ⟨g,le_sumIdeal_left (isCoherent_pullback (projection_contMDiff U)
    hQ.isWellFormed.isCoherent) z g hg,hfreq⟩

private theorem normal_zero_iff {n : ℕ} {U : Opens (ComplexModel n)} (z : productOpen U) :
    relativeNormalCoordinate U z=0 ↔ actualJointNormalProjection n 1 z.val=0 := by
  constructor
  · intro h
    ext i
    have hi : i=0 := Fin.eq_zero i
    subst i
    simpa [relativeNormalCoordinate,addedCoordinate,
      HironakaActualGraphFunctionalIdeal.graphFunction,zeroFunction] using h
  · intro h
    have he := congrArg (fun v : ComplexModel 1 => v 0) h
    simpa [relativeNormalCoordinate,addedCoordinate,
      HironakaActualGraphFunctionalIdeal.graphFunction,zeroFunction] using he

/-- Intersecting the proper normal cylinder with the true normal zero
set gives the actual lifted source carrier. -/
theorem normal_contact_carrier {n : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) :
    (properNormalMarked Q).N∩{z | relativeNormalCoordinate U z=0}=liftedCarrier Q.N := by
  ext z
  exact and_congr_right (fun _ => normal_zero_iff z)

/-- The real normal section, not the cylinder itself, has maximal contact
with the actual padded whole record and its complete ordered boundary. -/
theorem properNormalMarked_maxContact {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    MaxContact (Y := CMfd.of (n := n+1) (productOpen U)) (properNormalMarked Q) (liftedCarrier Q.N) := by
  have h := maxContact_base (Y := CMfd.of (n := n+1) (productOpen U))
    (properNormalMarked Q) (padding_coherent hQ.isWellFormed.isCoherent Q.d)
    (properNormalMarked_tangent Q (lt_of_lt_of_le Nat.zero_lt_one hQ.one_le_d))
  rw [inter_univ,normal_contact_carrier] at h
  exact h

private theorem normal_power_cosupport {n : ℕ} (U : Opens (ComplexModel n)) (N : Set (productOpen U))
    (d : ℕ) (hd : 0 < d) :
    cosupport (n+1) N
      (finiteFunctionIdeal (fun _ : Unit => fun z => relativeNormalCoordinate U z^d)) d=
      N∩{z | relativeNormalCoordinate U z=0} := by
  ext z
  have hhol : HolomorphicAt (n+1) (relativeNormalCoordinate U) z :=
    Eventually.of_forall (normalCoordinate_mdifferentiable U)
  constructor
  · intro hz
    have hm : (finiteFunctionIdeal (fun _ : Unit => fun z => relativeNormalCoordinate U z^d)).mem z
        (fun w => relativeNormalCoordinate U w^d) :=
      isInSpanAt_self ⟨(),rfl⟩ (holomorphicAt_pow hhol d)
    have hzero := (vanishesToOrderOn_one_iff hz.1 (holomorphicAt_pow hhol d)).mp
      ((hz.2 _ hm).mono hd)
    exact ⟨hz.1,eq_zero_of_pow_eq_zero hzero⟩
  · rintro ⟨hzN,hzero⟩
    have hp := mem_pointIdeal_of_apply_eq_zero hhol hzero
    have hPow := HomogenizedIdeal.pow_mem_idealPow hp hhol d
    refine ⟨hzN,fun g hg => IsInSpanAt.vanishesToOrderOn hg ?_⟩
    rintro _ ⟨_i,rfl⟩
    exact ⟨_,hPow,Eventually.of_forall (fun _ _ => rfl)⟩

private theorem projection_section {n : ℕ} (U : Opens (ComplexModel n)) (x : U) :
    projection U (zeroSection U x)=x := by
  apply Subtype.ext
  exact tangentProjection_tangentInclusion n 1 x.val

private theorem section_projection {n : ℕ} (U : Opens (ComplexModel n))
    (z : productOpen U) (hz : relativeNormalCoordinate U z=0) :
    zeroSection U (projection U z)=z := by
  have hZero := (normal_zero_iff z).mp hz
  apply Subtype.ext
  change tangentInclusion n 1 (tangentProjection n 1 z.val)=z.val
  simpa only [HironakaActualIntrinsicStableAmbientIso.join,hZero,map_zero,add_zero]
    using join_projections (n := n) (m := 1) z.val

/-- ENTIRE original cosupport of the ACTUAL proper-cylinder normal padding.
No radical or support substitution is made in either whole ideal. -/
theorem properNormalMarked_cosupp {n k : ℕ} {U : Opens (ComplexModel n)}
    (Q : MarkedIdeal n U) (hQ : IsInvDomain k Q) :
    (properNormalMarked Q).cosupp=zeroSection U '' Q.cosupp := by
  have hLeft := isCoherent_pullback (projection_contMDiff U) hQ.isWellFormed.isCoherent
  have hNormal := isCoherent_finiteFunctionIdeal (n := n+1)
    (fun _ : Unit => fun z : productOpen U => relativeNormalCoordinate U z^Q.d)
    (fun _ => (normalCoordinate_mdifferentiable U).pow Q.d)
  change cosupport (n+1) (projection U ⁻¹' Q.N)
    (sumIdeal (GermIdeal.pullback (m := n+1) (projection U) Q.ideal)
      (finiteFunctionIdeal (fun _ : Unit => fun z => relativeNormalCoordinate U z^Q.d))) Q.d=_
  rw [cosupport_sumIdeal (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hLeft hg)
      (fun _ _ hg => GermIdeal.IsCoherent.holomorphicAt_mem hNormal hg),
    cosupport_preimage_eq (projection_isSubmersion (U := U)) hQ.isWellFormed.isCoherent Q.N,
    normal_power_cosupport U _ Q.d (lt_of_lt_of_le Nat.zero_lt_one hQ.one_le_d)]
  ext z
  constructor
  · rintro ⟨hz,_hzN,hzero⟩
    exact ⟨projection U z,hz,section_projection U z hzero⟩
  · rintro ⟨x,hx,rfl⟩
    refine ⟨?_,?_,?_⟩
    · simpa only [Set.mem_preimage,projection_section,MarkedIdeal.cosupp] using hx
    · simpa only [Set.mem_preimage,projection_section] using Q.cosupp_subset_N hx
    · apply (normal_zero_iff _).mpr
      simp only [zeroSection,actualJointNormalProjection_tangent]

end
end Hironaka.HironakaG1ProperCarrierNormalContact
