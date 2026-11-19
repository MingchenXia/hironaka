import Hironaka.Analytic.Unibranch.HironakaG10LocEuclideanCartan
import Hironaka.Resolution.HironakaG10SmoothBaseQuotientFlatCriterion

/-! Actual whole-quotient flatness is open over an arbitrary smooth analytic
base, using the literal first-projection stalk action. -/

set_option autoImplicit false
open Set Filter
open scoped Topology Matrix

namespace Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen
noncomputable section
open Hironaka Hironaka
  HolGerm OkaRelationSheaf OkaGermBridge HironakaRelativeNormalIdeal
  HironakaActualCentreJointJets HironakaHolomorphicJetChartInvariance
  HironakaG10FlatGermChain HironakaG10FlatResolutionStart
  HironakaG10FlatPrivilegedNbhd HironakaG10LocSheafExact HironakaG10LocFibreOpen
  HironakaG10SmoothBaseFibreExactness HironakaG10SmoothBaseQuotientFlatCriterion

def splitModel (d t : ℕ) :
    ComplexModel (d + t) ≃L[ℂ] ComplexModel d × ComplexModel t :=
  EuclideanSpace.finAddEquivProd.toContinuousLinearEquiv

theorem splitModel_fst (d t : ℕ) (w : ComplexModel (d + t)) :
    (splitModel d t w).1 = tangentProjection d t w := by
  rfl

theorem tangentProjection_splitModel_symm (d t : ℕ) (w : ComplexModel d × ComplexModel t) :
    tangentProjection d t ((splitModel d t).symm w) = w.1 := by
  rw [← splitModel_fst, ContinuousLinearEquiv.apply_symm_apply]

theorem splitModel_normalInclusion (d t : ℕ) (z : ComplexModel t) :
    splitModel d t (actualJointNormalInclusion d t z) = (0, z) := by
  apply Prod.ext
  · rw [splitModel_fst, tangentProjection_actualJointNormalInclusion]
  · ext i
    simp [splitModel, EuclideanSpace.finAddEquivProd, EuclideanSpace.sumEquivProd,
      LinearIsometryEquiv.piLpCongrLeft_apply, actualJointNormalInclusion_normal]

def basePullback (d t : ℕ) :
    HolGerm (ComplexModel d) →+* HolGerm (ComplexModel d × ComplexModel t) :=
  HolGerm.comap (ContinuousLinearMap.fst ℂ (ComplexModel d) (ComplexModel t))

def ambientGermEquiv (d t : ℕ) :
    HolGerm (ComplexModel (d + t)) ≃+* HolGerm (ComplexModel d × ComplexModel t) :=
  HolGerm.comapEquiv (splitModel d t).symm

theorem ambientGermEquiv_tangentPullback (d t : ℕ) (a : HolGerm (ComplexModel d)) :
    ambientGermEquiv d t (tangentPullback d t a) = basePullback d t a := by
  induction a using HolGerm.induction_on with
  | h f hf =>
    change HolGerm.mk (fun w => f (tangentProjection d t ((splitModel d t).symm w)))
      (eventually_differentiableAt_comp_clm
        ((tangentProjection d t).comp (splitModel d t).symm.toContinuousLinearMap) hf) =
      HolGerm.mk (fun w => f w.1)
        (eventually_differentiableAt_comp_clm
          (ContinuousLinearMap.fst ℂ (ComplexModel d) (ComplexModel t)) hf)
    apply HolGerm.mk_eq_mk_iff.mpr
    exact Eventually.of_forall fun w => congrArg f (tangentProjection_splitModel_symm d t w)

/-- The local base action is literally the actual first projection at the actual point. -/
theorem basePullback_germAt_fst (d t : ℕ) (p : ComplexModel d × ComplexModel t)
    (f : ComplexModel d → ℂ) (hf : HolAt f p.1) :
    basePullback d t (germAt p.1 f) = germAt p (fun q => f q.1) := by
  have hfp : HolAt (fun q : ComplexModel d × ComplexModel t => f q.1) p :=
    hf.comp continuous_fst (fun _ => differentiableAt_fst)
  rw [basePullback, germAt_of_holAt hf, germAt_of_holAt hfp, HolGerm.comap_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun _ => rfl

def centredChart (d t : ℕ) (p : ComplexModel d × ComplexModel t) :
    ComplexModel (d + t) ≃ₜ ComplexModel d × ComplexModel t where
  toFun w := p + splitModel d t w
  invFun q := (splitModel d t).symm (q - p)
  left_inv w := by simp
  right_inv q := by simp
  continuous_toFun := continuous_const.add (splitModel d t).continuous
  continuous_invFun := (splitModel d t).symm.continuous.comp (continuous_id.sub continuous_const)

theorem centredChart_zero (d t : ℕ) (p : ComplexModel d × ComplexModel t) :
    centredChart d t p 0 = p := by simp [centredChart]

theorem differentiable_centredChart (d t : ℕ) (p : ComplexModel d × ComplexModel t)
    (w : ComplexModel (d + t)) : DifferentiableAt ℂ (centredChart d t p) w :=
  (differentiableAt_const p).add (splitModel d t).differentiableAt

theorem differentiable_centredChart_symm (d t : ℕ) (p q : ComplexModel d × ComplexModel t) :
    DifferentiableAt ℂ (centredChart d t p).symm q :=
  (splitModel d t).symm.differentiableAt.comp q (differentiableAt_id.sub (differentiableAt_const p))

def centredMatrix {a b : ℕ} (d t : ℕ)
    (F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (p : ComplexModel d × ComplexModel t) : Fin a → Fin b → ComplexModel (d + t) → ℂ :=
  fun i j => F i j ∘ centredChart d t p

theorem holAt_centredMatrix {a b : ℕ} (d t : ℕ)
    (F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (p : ComplexModel d × ComplexModel t) (hF : ∀ i j, HolAt (F i j) p) :
    ∀ i j, HolAt (centredMatrix d t F p i j) 0 := by
  intro i j
  have h : HolAt (F i j) (centredChart d t p 0) := by rw [centredChart_zero]; exact hF i j
  exact h.comp (centredChart d t p).continuous (differentiable_centredChart d t p)

def idealAt {b : ℕ} (d t : ℕ)
    (F : Fin 1 → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (p : ComplexModel d × ComplexModel t) : Ideal (HolGerm (ComplexModel d × ComplexModel t)) :=
  Ideal.span (Set.range fun j => germAt p (F 0 j))

def structureMapAt {b : ℕ} (d t : ℕ)
    (F : Fin 1 → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (p : ComplexModel d × ComplexModel t) :
    HolGerm (ComplexModel d) →+* HolGerm (ComplexModel d × ComplexModel t) ⧸ idealAt d t F p :=
  (Ideal.Quotient.mk (idealAt d t F p)).comp (basePullback d t)

def StalkFlatAt {b : ℕ} (d t : ℕ)
    (F : Fin 1 → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (p : ComplexModel d × ComplexModel t) : Prop := (structureMapAt d t F p).Flat

theorem ambientGermEquiv_centred_germ (d t : ℕ)
    (f : ComplexModel d × ComplexModel t → ℂ) (p : ComplexModel d × ComplexModel t)
    (hf : HolAt f p) :
    ambientGermEquiv d t (germAt 0 (f ∘ centredChart d t p)) = germAt p f := by
  have hcent : HolAt (f ∘ centredChart d t p) 0 := by
    have h : HolAt f (centredChart d t p 0) := by rw [centredChart_zero]; exact hf
    exact h.comp (centredChart d t p).continuous (differentiable_centredChart d t p)
  rw [germAt_of_holAt hcent, germAt_of_holAt hf]
  unfold ambientGermEquiv
  rw [HolGerm.comapEquiv_mk]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun q => by
    change f (p + splitModel d t (0 + (splitModel d t).symm q)) = f (p + q)
    rw [zero_add, ContinuousLinearEquiv.apply_symm_apply]

theorem map_centred_entryIdeal {b : ℕ} (d t : ℕ)
    (F : Fin 1 → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (p : ComplexModel d × ComplexModel t) (hF : ∀ i j, HolAt (F i j) p) :
    Ideal.map (ambientGermEquiv d t).toRingHom
      (HironakaG10LinearCurveMatrixPullback.entryIdeal d t (centredMatrix d t F p)) =
        idealAt d t F p := by
  unfold HironakaG10LinearCurveMatrixPullback.entryIdeal idealAt
  rw [Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  exact ambientGermEquiv_centred_germ d t (F 0 j) p (hF 0 j)

/-- The native criterion and the actual pointed quotient concern the same whole ideal and base map. -/
theorem native_flat_iff_stalkFlatAt {b : ℕ} (d t : ℕ)
    (F : Fin 1 → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (p : ComplexModel d × ComplexModel t) (hF : ∀ i j, HolAt (F i j) p) :
    (HironakaG10HirChartFlattener.chartMap d t
      (HironakaG10LinearCurveMatrixPullback.entryIdeal d t (centredMatrix d t F p))).Flat ↔
        StalkFlatAt d t F p := by
  let I := HironakaG10LinearCurveMatrixPullback.entryIdeal d t (centredMatrix d t F p)
  let e := Ideal.quotientEquiv I (idealAt d t F p) (ambientGermEquiv d t)
    (map_centred_entryIdeal d t F p hF).symm
  have he : e.toRingHom.comp (HironakaG10HirChartFlattener.chartMap d t I) =
      structureMapAt d t F p := by
    ext a
    change Ideal.Quotient.mk (idealAt d t F p) (ambientGermEquiv d t (tangentPullback d t a)) =
      Ideal.Quotient.mk (idealAt d t F p) (basePullback d t a)
    rw [ambientGermEquiv_tangentPullback]
  calc
    _ ↔ (e.toRingHom.comp (HironakaG10HirChartFlattener.chartMap d t I)).Flat :=
      (RingHom.Flat.comp_iff_of_bijective_left e.bijective).symm
    _ ↔ _ := Iff.of_eq (congrArg RingHom.Flat he)

theorem okaProperty_product_models (d t : ℕ) : OkaProperty (ComplexModel d × ComplexModel t) :=
  OkaProperty.of_homeomorph (splitModel d t).symm.toHomeomorph
    (fun _ => (splitModel d t).symm.differentiableAt)
    (fun _ => (splitModel d t).differentiableAt) (OkaCoherence.okaProperty_euclidean (d + t))

theorem holAt_fibMatrix {a b : ℕ} (d t : ℕ)
    (F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (p : ComplexModel d × ComplexModel t) (hF : ∀ i j, HolAt (F i j) p) :
    ∀ i j, HolAt (fib F p.1 i j) p.2 :=
  fun i j => (hF i j).comp (continuous_const.prodMk continuous_id)
    (fun _ => (differentiableAt_const p.1).prodMk differentiableAt_id)

/-- The whole normal-fibre germ matrix is the original fibre germ matrix at the actual point. -/
theorem germMat_normal_centred {a b : ℕ} (d t : ℕ)
    (F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (p : ComplexModel d × ComplexModel t) (hF : ∀ i j, HolAt (F i j) p) :
    germMat 0 (normalFamily d t (centredMatrix d t F p)) = germMat p.2 (fib F p.1) := by
  apply Matrix.ext
  intro i j
  change germAt 0 (normalFamily d t (centredMatrix d t F p) i j) = germAt p.2 (fib F p.1 i j)
  rw [germAt_of_holAt
      (holAt_normalFamily d t (centredMatrix d t F p) (holAt_centredMatrix d t F p hF) i j),
    germAt_of_holAt (holAt_fibMatrix d t F p hF i j)]
  apply HolGerm.mk_eq_mk_iff.mpr
  exact Eventually.of_forall fun z => by
    change F i j (p + splitModel d t (actualJointNormalInclusion d t (0 + z))) =
      F i j (p.1, p.2 + z)
    rw [zero_add, splitModel_normalInclusion]
    change F i j (p.1 + 0, p.2 + z) = F i j (p.1, p.2 + z)
    rw [add_zero]

theorem normal_exact_iff_fibreExact {a b c : ℕ} (d t : ℕ)
    (F : Fin a → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (G : Fin b → Fin c → ComplexModel d × ComplexModel t → ℂ)
    (p : ComplexModel d × ComplexModel t) (hF : ∀ i j, HolAt (F i j) p)
    (hG : ∀ j k, HolAt (G j k) p) :
    (∀ v : Fin b → ComplexModel t → ℂ,
      IsRelationAt (normalFamily d t (centredMatrix d t F p)) 0 v →
        IsCombinationAt (columns (normalFamily d t (centredMatrix d t G p))) 0 v) ↔
      FibreExactAt G F p.1 p.2 := by
  have h1 := exact_iff_matExact
    (holAt_normalFamily d t (centredMatrix d t F p) (holAt_centredMatrix d t F p hF))
    (holAt_normalFamily d t (centredMatrix d t G p) (holAt_centredMatrix d t G p hG))
  have h2 := exact_iff_matExact (holAt_fibMatrix d t F p hF) (holAt_fibMatrix d t G p hG)
  rw [germMat_normal_centred d t F p hF, germMat_normal_centred d t G p hG] at h1
  exact h1.trans h2.symm

/-- Exact-start flatness is actual flatness of the same whole quotient with its actual stalk action. -/
theorem fibreFlatAt_iff_stalkFlatAt {b : ℕ} (d t : ℕ)
    (F : Fin 1 → Fin b → ComplexModel d × ComplexModel t → ℂ)
    (p : ComplexModel d × ComplexModel t) (hF : ∀ i j, HolAt (F i j) p) :
    FibreFlatAt F p ↔ StalkFlatAt d t F p := by
  obtain ⟨W, hW, hpW, c, G, hstart⟩ := exists_exactStartOn (okaProperty_product_models d t) F p hF
  have hG : ∀ j k, HolAt (G j k) p := fun j k => holAt_of_differentiableOn hW (hstart.holG j k) hpW
  have hpred : FibreFlatAt F p ↔ FibreExactAt G F p.1 p.2 := by
    constructor
    · intro h
      exact (fibreFlatAt_iff_forall.mp h).2 c G W hW hpW hstart
    · intro h
      exact ⟨c, G, W, hW, hpW, hstart, h⟩
  have hnstart := exactStartOn_comp_homeomorph (centredChart d t p)
    (differentiable_centredChart d t p) (differentiable_centredChart_symm d t p) hstart
  have h0 : (0 : ComplexModel (d + t)) ∈ (centredChart d t p) ⁻¹' W := by
    simpa only [mem_preimage, centredChart_zero] using hpW
  have hcrit := chartMap_flat_iff_normal_fibre_exact d t
    (centredMatrix d t F p) (centredMatrix d t G p)
    (hW.preimage (centredChart d t p).continuous) h0 hnstart
  exact hpred.trans ((normal_exact_iff_fibreExact d t F G p hF hG).symm.trans
    (hcrit.symm.trans (native_flat_iff_stalkFlatAt d t F p hF)))

/-- Actual `RingHom.Flat` is open on the holomorphic product domain, in every smooth base dimension. -/
theorem isOpen_stalkFlatLocus {b : ℕ} (d t : ℕ)
    (F : Fin 1 → Fin b → ComplexModel d × ComplexModel t → ℂ)
    {U : Set (ComplexModel d × ComplexModel t)} (hU : IsOpen U)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U) :
    IsOpen {p | p ∈ U ∧ StalkFlatAt d t F p} := by
  have hSet : {p | p ∈ U ∧ StalkFlatAt d t F p} = U ∩ {p | FibreFlatAt F p} := by
    ext p
    constructor
    · rintro ⟨hp, hflat⟩
      exact ⟨hp, (fibreFlatAt_iff_stalkFlatAt d t F p
        (fun i j => holAt_of_differentiableOn hU (hF i j) hp)).mpr hflat⟩
    · rintro ⟨hp, hflat⟩
      exact ⟨hp, (fibreFlatAt_iff_stalkFlatAt d t F p
        (fun i j => holAt_of_differentiableOn hU (hF i j) hp)).mp hflat⟩
  rw [hSet]
  exact hU.inter (HironakaG10LocEuclideanCartan.isOpen_fibreFlatAt F)

/-- Uniform actual whole-quotient flatness near any compact subset of a fibre. -/
theorem eventually_stalkFlatAt_compact {b : ℕ} (d t : ℕ)
    (F : Fin 1 → Fin b → ComplexModel d × ComplexModel t → ℂ)
    {U : Set (ComplexModel d × ComplexModel t)} (hU : IsOpen U)
    (hF : ∀ i j, DifferentiableOn ℂ (F i j) U)
    {K : Set (ComplexModel t)} (hK : IsCompact K) {s₀ : ComplexModel d}
    (h : ∀ z ∈ K, (s₀, z) ∈ U ∧ StalkFlatAt d t F (s₀, z)) :
    ∀ᶠ s in 𝓝 s₀, ∀ z ∈ K, (s, z) ∈ U ∧ StalkFlatAt d t F (s, z) :=
  HironakaG10LocEuclideanCartan.eventually_forall_mem_of_isOpen hK
    (isOpen_stalkFlatLocus d t F hU hF) h

end
end Hironaka.Analytic.Unibranch.HironakaG10SmoothBaseFlatOpen
