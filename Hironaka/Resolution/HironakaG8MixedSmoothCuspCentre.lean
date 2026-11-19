import Hironaka.Resolution.HironakaG8InitialSmoothSpecialCentre
import Hironaka.Resolution.HironakaG8OddCuspGeometricSource
import Hironaka.Analytic.HolomorphicGermReducednessBridge
import Hironaka.Resolution.HironakaPrincipalizationBoundary

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

open Set Filter TopologicalSpace Classical
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaG8MixedSmoothCuspCentre
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals MarkedIdeals.MarkedIdeal ResolutionInvariantSpec CanonicalCentres
  GermIdealOrder DivisorExponentAlong DivisorExponent IdealWeightPowers OrderMultiplicativity
  HironakaG8NativeCuspDiagram HironakaG8OddCuspVanishingStalk HironakaG8OddCuspGeometricSource HironakaEmbeddedAnalytic
  HironakaG8InitialSmoothSpecialCentre HironakaEmbeddedBoundary HironakaPrincipalizationBoundary
  NonmonomialOrderLocal HironakaSharpOriginalProductTraceOrder
  NormalCrossings HolomorphicGermReducednessBridge CodimOneSupport ResolutionDriver ResolutionInvariantDriver

abbrev X := CMfd.of (n := 3) (ComplexModel 3)

def w (z : X) : ℂ := z 2
def plane : Set X := {z | w z = 1}
def source : Set X := embeddedCuspSet 5 ∪ plane
def smoothPoint : X := PiLp.single 2 (2 : Fin 3) (1 : ℂ)
def M : MarkedIdeal 3 X := ⟨univ,[],vanishingIdeal (n := 3) source,1⟩
private def f (z : X) : ℂ := w z * (w z - 1)

private theorem w_hol : Differentiable ℂ w :=
  (EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).differentiable

private theorem f_hol : Differentiable ℂ f := by
  intro x
  exact (w_hol x).mul ((w_hol x).sub_const 1)

private theorem w_cusp {x : X} (hx : x ∈ embeddedCuspSet 5) : w x = 0 := hx 1

private theorem w_smooth : w smoothPoint = 1 := by simp [w,smoothPoint]

private theorem plane_analytic : IsComplexAnalyticSubset (n := 3) plane := by
  intro x
  have hc : (complexChartAt (n := 3) x).val = OpenPartialHomeomorph.refl (ComplexModel 3) := by
    simp [complexChartAt]
  refine ⟨{ generatorCount := 1
            generator := fun _ z => w z - 1
            coordinateNeighborhood := univ
            isOpen_coordinateNeighborhood := isOpen_univ
            center_mem_coordinateNeighborhood := mem_univ _
            coordinateNeighborhood_subset_target := by rw [hc]; exact subset_rfl
            generator_holomorphic := fun _ => (w_hol.sub_const 1).differentiableOn
            zeroLocus := ?_ }⟩
  intro y _ _
  rw [hc]
  change w y = 1 ↔ ∀ _ : Fin 1, w y - 1 = 0
  exact ⟨fun h _ => sub_eq_zero.mpr h,fun h => sub_eq_zero.mp (h 0)⟩

theorem source_analytic : IsComplexAnalyticSubset (n := 3) source :=
  HironakaEmbeddedAnalyticLocal.isComplexAnalyticSubset_union (embedded_cusp_isAnalytic 5) plane_analytic

private theorem f_mem (x : X) : M.ideal.mem x f := by
  refine ⟨Eventually.of_forall (fun z => (f_hol z).mdifferentiableAt), Eventually.of_forall ?_⟩
  intro z hz
  rcases hz with hz | hz
  · simp [f,w_cusp hz]
  · change w z = 1 at hz
    simp [f,hz]

private theorem f_deriv (x : X) : fderiv ℂ f x smoothPoint = w x - 1 + w x := by
  have h := (w_hol x).hasFDerivAt
  have h' := h.mul (h.sub_const (1 : ℂ))
  have he := congrArg (fun L : ComplexModel 3 →L[ℂ] ℂ => L smoothPoint) h'.fderiv
  have hw : fderiv ℂ w x smoothPoint = 1 := by
    have hw' := (EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).hasFDerivAt (x := x)
    exact (congrArg (fun L : ComplexModel 3 →L[ℂ] ℂ => L smoothPoint) hw'.fderiv).trans w_smooth
  change fderiv ℂ f x smoothPoint = _ at he
  simpa [hw, mul_comm, add_comm] using he

private theorem f_deriv_ne {x : X} (hx : w x = 0 ∨ w x = 1) :
    fderiv ℂ f x smoothPoint ≠ 0 := by
  rw [f_deriv]
  rcases hx with hx | hx <;> simp [hx]

theorem source_domain : IsInvDomain 3 M := by
  apply isInvDomain_univ_of_isSNCDivisor (CartanIrreducible.cartanCoherence source source_analytic)
    _ isSNCDivisor_nil
  intro x
  refine ⟨f,f_mem x,?_⟩
  rw [Filter.Frequently]
  intro h
  have hz : f =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := h.mono fun _ hy => by simpa using hy
  have h0 : f x = 0 := hz.self_of_nhds
  have hf : w x = 0 ∨ w x = 1 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.mp h)
  apply f_deriv_ne hf
  rw [hz.fderiv_eq (𝕜 := ℂ), fderiv_const_apply]
  rfl

theorem source_cosupport : M.cosupp = source :=
  cosupp_mk_vanishingIdeal source_analytic.isClosed []

private theorem f_not_order_two (x : X) (hx : x ∈ source) :
    ¬ VanishesToOrderOn 3 univ x 2 f := by
  intro h
  obtain ⟨g,hg,heg⟩ := h
  have he : f =ᶠ[𝓝 x] g := heg.mono fun _ hh => hh trivial
  have hgh := holomorphicAt_of_mem_idealPow hg
  have h1 := (mem_idealPow_pointIdeal_iff_iteratedFDeriv hgh 2).mp hg 1 (by decide)
  have hc : (complexChartAt (n := 3) x).val = OpenPartialHomeomorph.refl (ComplexModel 3) := by
    simp [complexChartAt]
  rw [hc] at h1
  have hd := congrArg (fun L : ContinuousMultilinearMap ℂ (fun _ : Fin 1 => ComplexModel 3) ℂ =>
    L (fun _ => smoothPoint)) h1
  apply f_deriv_ne (hx.elim (fun h => Or.inl (w_cusp h)) Or.inr)
  rw [he.fderiv_eq (𝕜 := ℂ)]
  simpa [iteratedFDeriv_one_apply] using hd

theorem source_uniform_nonmonomial_order (x : X) (hx : x ∈ M.cosupp) : nmOrd M x = 1 := by
  have hT (r : ℕ) : x ∈ cosupport 3 univ M.ideal r ↔ r ≤ nmOrd M x :=
    ordinaryTraceOrder_cosupport_iff (X := X) source_domain.isWellFormed.isClosedSubmanifold_N
      source_domain.isWellFormed.isCoherent source_domain.isNonzeroAlongAt (mem_univ x) r
  have h1 := (hT 1).mp hx
  have h2 : ¬ 2 ≤ nmOrd M x := by
    intro hh
    exact f_not_order_two x (source_cosupport ▸ hx) (((hT 2).mpr hh).2 f (f_mem x))
  omega

theorem smoothPoint_regular_source : RegularAtDim (n := 3) source smoothPoint 2 := by
  have hc : (complexChartAt (n := 3) smoothPoint).val = OpenPartialHomeomorph.refl (ComplexModel 3) := by
    simp [complexChartAt]
  have hP : RegularAtDim (n := 3) plane smoothPoint (3-1) := by
    apply regularAtDim_of_eventuallyEq_unit_mul_coordinate
      (N := univ) (f := fun z : X => w z - 1) (u := fun _ => 1) (j := 2)
      isOpen_univ (mem_univ _) (by rw [hc]; exact subset_rfl)
      (w_hol.sub_const 1).differentiableOn
    · intro y _ _
      rw [hc]
      exact sub_eq_zero.symm
    · exact w_smooth
    · exact differentiableAt_const _
    · simp
    · rw [hc]
      exact Eventually.of_forall (fun z => by simp [w,smoothPoint])
  apply regularAtDim_of_eventually_mem_iff _ hP
  have hNear := w_hol.continuous.continuousAt.eventually
    (isOpen_ne.mem_nhds (show w smoothPoint ≠ 0 by simp [w_smooth]))
  exact hNear.mono fun z hz => ⟨Or.inr,fun h => h.elim (fun hc => (hz (w_cusp hc)).elim) id⟩

theorem origin_singular_source : (0 : X) ∈ singularSet (n := 3) source := by
  have hs := embedded_odd_cusp_singular_at_zero 5 (by decide) (by decide)
  rw [mem_singularSet_iff] at hs ⊢
  refine ⟨Or.inl hs.1,fun j hj => hs.2 j (regularAtDim_of_eventually_mem_iff ?_ hj)⟩
  have hNear := w_hol.continuous.continuousAt.eventually
    (isOpen_ne.mem_nhds (show w (0 : X) ≠ 1 by simp [w]))
  exact hNear.mono fun z hz => ⟨fun h => h.elim id (fun h => (hz h).elim),Or.inl⟩

/-- The two-point compact task contains a genuine singular point. Every
occupied conventional original mark-one canonical first step must
nevertheless contain the specified smooth hypersurface point. -/
theorem compact_mixed_source_canonical_first_centre
    {Z : CMfd.{0} 3} (D : Set X) (hD : D.Nonempty) (π : Z → X) (hπ : IsBlowupAlong 3 D π)
    (hCan : IsCanonical M ((canonicalInvariant 3).inv M) (.step .refl D π hπ)) :
    let K : Set X := {0,smoothPoint}
    IsCompact K ∧ (K ∩ singularSet (n := 3) source).Nonempty ∧
      smoothPoint ∈ D ∧ smoothPoint ∉ singularSet (n := 3) source := by
  intro K
  have hR := smoothPoint_regular_source
  have hCan' : IsCanonical M ((invFamily (by decide : 0 < 3) 3).inv M) (.step .refl D π hπ) := hCan
  refine ⟨(isCompact_singleton.insert _),
    ⟨0,by simp [K],origin_singular_source⟩,?_,?_⟩
  · apply initial_regular_hypersurface_in_canonical_centre (k := 2) (j := 2)
      (by decide : 0 < 3) M source_domain rfl rfl source_uniform_nonmonomial_order smoothPoint
      (AnalyticIrreducibleComponents.regularAtDim_univ _) _ D hD π hπ hCan'
    rw [source_cosupport]
    exact hR
  · intro h
    exact (mem_singularSet_iff.mp h).2 2 hR

/-- The mixed compact task admits a genuine occupied original canonical
first blowup. Its centre necessarily contains the smooth point. -/
theorem exists_compact_mixed_source_canonical_first_blowup :
    ∃ (Z : CMfd.{0} 3) (D : Set X) (π : Z → X) (hπ : IsBlowupAlong 3 D π),
      D.Nonempty ∧ smoothPoint ∈ D ∧
      IsCanonical M ((canonicalInvariant 3).inv M) (.step .refl D π hπ) := by
  let I := invFamily (by decide : 0 < 3) 3
  let T : BlowupTower X X := .refl
  let D := maxLocus (I.inv M T) M.cosupp
  have hr : RegularAtDim (n := 3) M.cosupp smoothPoint 2 :=
    source_cosupport.symm ▸ smoothPoint_regular_source
  have hMax : smoothPoint ∈ D :=
    initial_regular_hypersurface_is_original_maximum (k := 2) (j := 2)
      (by decide : 0 < 3) M source_domain rfl rfl source_uniform_nonmonomial_order smoothPoint
      (AnalyticIrreducibleComponents.regularAtDim_univ _) hr
  have hAdm : M.IsAdmissibleCentre D :=
    I.isInvValue.isAdmissibleCentre_maxLocus source_domain T trivial trivial
  have hThin : interior D = ∅ := interior_maxLocus_eq_empty source_domain T trivial (I.inv M T)
  obtain ⟨Z,π,hπ⟩ := exists_blowup D hAdm.1 hThin
  exact ⟨Z,D,π,hπ,⟨smoothPoint,hMax⟩,hMax,⟨trivial,Or.inr rfl⟩⟩

/-- Restricting to any open neighborhood of the compact two-point task
still leaves a smooth maximizer. Thus a genuine occupied first step of
the conventional original evaluator cannot be a singular-only step on
any such neighborhood. -/
theorem mixed_compact_task_no_singular_only_canonical_first_step
    (U : Opens X) (h0 : (0 : X) ∈ U) (hp : smoothPoint ∈ U)
    {Z : CMfd.{0} 3} (D : Set U) (hD : D.Nonempty) (π : Z → U)
    (hπ : IsBlowupAlong 3 D π) :
    let W := (Subtype.val : U → X) ⁻¹' source
    let P : MarkedIdeal 3 (CMfd.of (n := 3) U) :=
      MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M
    (⟨0,h0⟩ : U) ∈ singularSet (n := 3) W ∧
    ¬ (IsCanonical P ((canonicalInvariant 3).inv P) (.step .refl D π hπ) ∧
      D ⊆ singularSet (n := 3) W) := by
  intro W P
  constructor
  · rw [mem_singularSet_iff]
    have h := (mem_singularSet_iff.mp origin_singular_source)
    exact ⟨h.1,fun j hj => h.2 j (AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mp hj)⟩
  · rintro ⟨hCan,hSing⟩
    have hP := InvDomainTowerAlong.isInvDomain_pullback_val U source_domain
    have hCos := MarkedIdealRestrictOpen.cosupp_pullback_val M
      (fun _ _ hg => RelativePrincipalizationSpan.GermIdeal.IsCoherent.holomorphicAt_mem
        source_domain.isWellFormed.isCoherent hg) U
    have hUniform (x : U) (hx : x ∈ P.cosupp) : nmOrd P x = 1 := by
      rw [nmOrd_pullback_val (by decide : 0 < 3) source_domain.isWellFormed source_domain.isNonzeroAlongAt U x]
      change x ∈ (MarkedIdealBiholomorphism.MarkedIdeal.pullback (Subtype.val : U → X) M).cosupp at hx
      rw [hCos] at hx
      exact source_uniform_nonmonomial_order x.val hx
    let x : U := ⟨smoothPoint,hp⟩
    have hR : RegularAtDim (n := 3) W x 2 :=
      AnalyticSubsetOpens.regularAtDim_preimage_val_iff.mpr smoothPoint_regular_source
    have hRCos : RegularAtDim (n := 3) P.cosupp x 2 := by
      change RegularAtDim (n := 3) (MarkedIdealBiholomorphism.MarkedIdeal.pullback
        (Subtype.val : U → X) M).cosupp x 2
      rw [hCos,source_cosupport]
      exact hR
    have hN : RegularAtDim (n := 3) P.N x (2+1) := by
      change RegularAtDim (n := 3) ((Subtype.val : U → X) ⁻¹' (univ : Set X)) x 3
      rw [preimage_univ]
      exact AnalyticIrreducibleComponents.regularAtDim_univ _
    have hxD := initial_regular_hypersurface_in_canonical_centre
      (k := 2) (j := 2) (by decide : 0 < 3) P hP rfl rfl hUniform x hN hRCos D hD π hπ hCan
    exact (mem_singularSet_iff.mp (hSing hxD)).2 2 hR

end
end Hironaka.HironakaG8MixedSmoothCuspCentre
