import TranscendentalNakamaye.Pending.HironakaActualCentreWeightedControlledStalk

/-! Fixed mark ONE normal-generator control in actual native blowup charts.
The old prescribed-base controlled trace and whole split remain open.
Blueprint: hironaka-disjoint-controlled-normal-pivot-extension.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
namespace TranscendentalNakamaye.Pending.HironakaDisjointControlledNormalPivot
noncomputable section
open FirstPass FirstPass.HolomorphicIdealSheaves FirstPass.BlowupSequences
  HolGerm RelativePrincipalizationSpan GermIdealPullbackCalculus
  HironakaSmoothSubmersionGermIdealColon HironakaActualSingularChartTransport
  HironakaActualAnalyticBlowupTaylor HironakaActualCentreWeightedControlledStalk
  HironakaHolomorphicJetMonomialSpan HironakaHolomorphicJetChartInvariance
  BlowupControlledTransform BlowupExceptionalDivisor IdealWeightPowers
  InvertibleIdealQuotient CoherentIdealColon BlowupFlatCoordinates
  HironakaRelativeNormalIdeal
variable {d : ℕ} {Y : Type} [TopologicalSpace Y]
  [ChartedSpace (ComplexModel (d+1)) Y] [IsComplexManifold (d+1) Y]

private theorem inverse_square (U : TopologicalSpace.Opens (ComplexModel (d+1)))
    (π : Y → U) (y : Y) (S : Set (Fin (d+1))) (e : Fin (d+1)) (b : Fin (d+1) → ℂ)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+1)) y y))
    (hsrc : Θ.source ⊆ (chartAt (ComplexModel (d+1)) y).target)
    (h0 : Θ.toFun (chartAt (ComplexModel (d+1)) y y)=0)
    (hsquare : ∀ z : Y, z  ∈  (chartAt (ComplexModel (d+1)) y).source →
      chartAt (ComplexModel (d+1)) y z  ∈  Θ.source →
      (π z : ComplexModel (d+1))=actualAnalyticBlowupMap S e b (Θ.toFun (chartAt (ComplexModel (d+1)) y z))) :
    ∀ᶠ v in 𝓝 (0 : ComplexModel (d+1)),
      (π (inverseCoordinates Θ v) : ComplexModel (d+1))=actualAnalyticBlowupMap S e b v := by
  have htar : (0 : ComplexModel (d+1))  ∈  Θ.target := by
    simpa only [h0] using Θ.mapsTo_toFun Θ.center_mem_source
  filter_upwards [Θ.isOpen_target.mem_nhds htar] with v hv
  have hm:=flatInverse_mem Θ hv hsrc
  have h:=hsquare (inverseCoordinates Θ v) hm.1.1 hm.1.2
  change (π (inverseCoordinates Θ v) : ComplexModel (d+1))=actualAnalyticBlowupMap S e b v
  simpa only [inverseCoordinates,hm.2] using h

/-- A source normal member produces its exact fixed-mark quotient in the
WHOLE actual controlled stalk, not an all-orders saturated ideal. -/
theorem normal_quotient_mem (U : TopologicalSpace.Opens (ComplexModel (d+1)))
    (k : ℕ) (hk : k ≤ d) (π : Y → U)
    (hπ : IsBlowupAlong (d+1) ((Subtype.val : U → ComplexModel (d+1)) ⁻¹'
      complexCoordinatePlane (d+1) k) π)
    (J : GermIdeal (d+1) U) (hJ : J.IsCoherent) (y : Y)
    (hnormal : J.mem (π y) (fun z : U => z.val (Fin.last d)))
    (e : Fin (d+1)) (he : k ≤ e.val) (b : Fin (d+1) → ℂ)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+1)) y y))
    (hsrc : Θ.source ⊆ (chartAt (ComplexModel (d+1)) y).target)
    (h0 : Θ.toFun (chartAt (ComplexModel (d+1)) y y)=0)
    (hsquare : ∀ z : Y, z  ∈  (chartAt (ComplexModel (d+1)) y).source →
      chartAt (ComplexModel (d+1)) y z  ∈  Θ.source →
      (π z : ComplexModel (d+1))=actualAnalyticBlowupMap {i : Fin (d+1) | k ≤ i.val} e b
        (Θ.toFun (chartAt (ComplexModel (d+1)) y z))) :
    (if e=Fin.last d then 1 else HolGerm.constHom (b (Fin.last d))+coordinateGerm (Fin.last d))  ∈  
      adaptedIdeal (controlledTransform hπ J 1) y Θ h0 := by
  let S : Set (Fin (d+1)):={i | k ≤ i.val}
  have heS : e  ∈  S:=he
  have hlast : Fin.last d  ∈  S:=hk
  have hfh : HolomorphicAt (d+1) (fun z : Y => (π z).val (Fin.last d)) y :=
    (GermIdeal.IsCoherent.holomorphicAt_mem hJ hnormal).comp_contMDiff
      (Eventually.of_forall fun _ => hπ.contMDiff.contMDiffAt)
  have hmem : (GermIdeal.pullback (m:=d+1) π J).mem y (fun z : Y => (π z).val (Fin.last d)) := by
    exact GermIdeal.mem_pullback_iff.mpr (isInSpanAt_self
      ⟨(fun z : U => z.val (Fin.last d)),hnormal,rfl⟩ hfh)
  have hG : adaptedGerm y Θ h0 (fun z : Y => (π z).val (Fin.last d)) hfh=
      actualAnalyticBlowupPullback S e b (coordinateGerm (Fin.last d)) := by
    unfold actualAnalyticBlowupPullback coordinateGerm
    rw [compAlgHom_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    exact (inverse_square U π y S e b Θ hsrc h0 hsquare).mono fun v hv =>
      congrArg (fun z : ComplexModel (d+1) => z (Fin.last d)) hv
  have hTotal : actualAnalyticBlowupPullback S e b (coordinateGerm (Fin.last d))  ∈  
      adaptedIdeal (GermIdeal.pullback (m:=d+1) π J) y Θ h0 := by
    rw [←hG]
    exact Ideal.subset_span ⟨_,hfh,hmem,rfl⟩
  have hExc:=actual_exceptional_power_stalk U y S e b Θ hsrc h0 hsquare heS hπ 1
  change adaptedIdeal (idealPow (exceptionalDivisor hπ).ideal 1) y Θ h0=Ideal.span {(coordinateGerm e)^1} at hExc
  unfold controlledTransform
  rw [adaptedIdeal_colon_eq _ _ (isCoherent_pullback hπ.contMDiff hJ)
    (isCoherent_idealPow (DivisorMetric.isCoherent_of_isInvertible (exceptionalDivisor hπ).isInvertible) 1),
    hExc,
    pow_one,Ideal.colon_span,Submodule.mem_colon_singleton]
  rw [actualAnalyticBlowupPullback_coordinate,if_pos hlast] at hTotal
  by_cases h : e=Fin.last d
  · subst e
    simpa [smul_eq_mul] using hTotal
  · have hne : Fin.last d  ≠  e:=Ne.symm h
    simpa [h,hne,smul_eq_mul,mul_comm] using hTotal

private theorem adapted_mem_eval_zero (A : GermIdeal (d+1) Y) (y : Y)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+1)) y y))
    (h0 : Θ.toFun (chartAt (ComplexModel (d+1)) y y)=0)
    (hcut : y ∈ GermIdealOrder.cosupport (d+1) univ A 1)
    {g : HolGerm (ComplexModel (d+1))} (hg : g ∈ adaptedIdeal A y Θ h0) : HolGerm.eval g=0 := by
  have hle : adaptedIdeal A y Θ h0 ≤ RingHom.ker (HolGerm.eval : HolGerm (ComplexModel (d+1)) →+* ℂ) := by
    apply Ideal.span_le.mpr
    rintro a ⟨F,hF,hmem,rfl⟩
    have hzero : F y=0 :=
      (GermIdealOrder.vanishesToOrderOn_one_iff (mem_univ y) hF).mp (hcut.2 F hmem)
    have hi : Θ.invFun 0=chartAt (ComplexModel (d+1)) y y := by
      rw [←h0,Θ.left_inv _ Θ.center_mem_source]
    change F ((chartAt (ComplexModel (d+1)) y).symm (Θ.invFun 0))=0
    rw [hi,(chartAt (ComplexModel (d+1)) y).left_inv (mem_chart_source _ y)]
    exact hzero
  exact hle hg

/-- At actual current cosupport points the real native blowup chart is
forced to have an old owner and zero new-normal direction. -/
theorem exists_actual_normal_free_controlled_chart
    (U : TopologicalSpace.Opens (ComplexModel (d+1))) (k : ℕ) (hk : k ≤ d)
    (π : Y → U)
    (hπ : IsBlowupAlong (d+1) ((Subtype.val : U → ComplexModel (d+1)) ⁻¹'
      complexCoordinatePlane (d+1) k) π)
    (J : GermIdeal (d+1) U) (hJ : J.IsCoherent) (y : Y)
    (hy : (π y : ComplexModel (d+1))=0)
    (hnormal : J.mem (π y) (fun z : U => z.val (Fin.last d)))
    (hcut : y ∈ GermIdealOrder.cosupport (d+1) univ (controlledTransform hπ J 1) 1) :
    ∃ (e : Fin (d+1)) (b : Fin (d+1) → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel (d+1)) y y))
      (h0 : Θ.toFun (chartAt (ComplexModel (d+1)) y y)=0),
      k ≤ e.val ∧ e.val<d ∧ b (Fin.last d)=0 ∧
      Θ.source ⊆ (chartAt (ComplexModel (d+1)) y).target ∧
      (∀ z : Y, z ∈ (chartAt (ComplexModel (d+1)) y).source →
        chartAt (ComplexModel (d+1)) y z ∈ Θ.source →
        (π z : ComplexModel (d+1))=actualAnalyticBlowupMap {i : Fin (d+1) | k ≤ i.val} e b
          (Θ.toFun (chartAt (ComplexModel (d+1)) y z))) ∧
      coordinateGerm (Fin.last d) ∈ adaptedIdeal (controlledTransform hπ J 1) y Θ h0 ∧
      RingHom.ker (planeTrace d 1).toRingHom ≤ adaptedIdeal (controlledTransform hπ J 1) y Θ h0 := by
  have h0U : (0 : ComplexModel (d+1)) ∈ U := by
    rw [←hy]
    exact (π y).property
  obtain ⟨e,b,Θ,h0,he,_hbt,_hbe,hsrc,hsquare,_hdummy⟩:=
    exists_actual_coordinate_centre_weighted_stalk U h0U k π hπ y hy
      (ι:=Fin 0) (fun _ => 1) (fun _ _ => 0) (fun i => Fin.elim0 i)
  have hnormalQ:=normal_quotient_mem U k hk π hπ J hJ y hnormal e he b Θ hsrc h0 hsquare
  have hne : e ≠ Fin.last d := by
    intro h
    have hunit : (1 : HolGerm (ComplexModel (d+1))) ∈ adaptedIdeal (controlledTransform hπ J 1) y Θ h0 := by
      simpa [h] using hnormalQ
    have hz:=adapted_mem_eval_zero (controlledTransform hπ J 1) y Θ h0 hcut hunit
    exact one_ne_zero (show (1 : ℂ)=0 from hz)
  have hless : e.val<d := by
    have hlt:=e.isLt
    have hn : e.val ≠ d := fun h => hne (Fin.ext h)
    omega
  have hb : b (Fin.last d)=0 := by
    have hz:=adapted_mem_eval_zero (controlledTransform hπ J 1) y Θ h0 hcut hnormalQ
    simpa [hne,coordinateGerm,HolGerm.eval_mk] using hz
  have hnorm : coordinateGerm (Fin.last d) ∈ adaptedIdeal (controlledTransform hπ J 1) y Θ h0 := by
    simpa [hne,hb] using hnormalQ
  refine ⟨e,b,Θ,h0,he,hless,hb,hsrc,hsquare,hnorm,?_⟩
  rw [←normalIdeal_eq_ker_planeTrace]
  apply Ideal.span_le.mpr
  rintro a ⟨j,rfl⟩
  have hj : j.natAdd d=Fin.last d := by
    apply Fin.ext
    have hjlt:=j.isLt
    dsimp only [Fin.natAdd,Fin.last]
    omega
  change coordinateGerm (j.natAdd d) ∈ adaptedIdeal (controlledTransform hπ J 1) y Θ h0
  rw [hj]
  exact hnorm

end
end TranscendentalNakamaye.Pending.HironakaDisjointControlledNormalPivot
