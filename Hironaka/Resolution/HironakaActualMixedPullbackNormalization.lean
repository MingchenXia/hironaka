import Hironaka.Resolution.HironakaActualProjectionTestRecord
import Hironaka.Resolution.HironakaActualExceptionalTestRecord
import Hironaka.Resolution.HironakaActualPowerBoundaryExponents

/-! Whole proper-carrier normalization survives the actual dimension-changing
projection and ordinary exceptional stages. Source restricted inclusions are
ordinary relations between current whole ideals, not future comparison packets.
Blueprint FIRST: hironaka-actual-mixed-pullback-normalization.tex. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualMixedPullbackNormalization
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers MarkedIdeals ResolutionInvariantSpec RelativePrincipalizationSpan
  InvertibleIdealQuotient GermIdealPullbackCalculus RestrictedIdealWeight
  RestrictLeCalculus IdealWeightPowers MarkedIdealOperationsAlong.MarkedIdeal
  HironakaActualProjectionTestRecord HironakaActualExceptionalTestRecord
  HironakaActualPowerBoundaryExponents HironakaSmoothSubmersionCoefficientIdeals
  HironakaAuxiliaryGraphGeometry ProductComplexManifold BlowupStrictSubmanifold
open scoped ProductComplexManifold

variable {n : ℕ} {X : CMfd.{u} n}

/-- A whole SOURCE restricted inclusion pulls back through an ordinary
actual holomorphic map with arbitrary source and target ambient dimensions. -/
theorem cross_dimension_restrictLe_pullback {m : ℕ} {Y : CMfd.{u} m} {f : Y → X}
    (hf : ContMDiff 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f)
    {V : Set X} {W : Set Y} (hWV : ∀ y ∈ W,f y ∈ V) {A B : GermIdeal n X}
    (hB : B.IsCoherent) (hAB : RestrictLe V A B) :
    RestrictLe W (GermIdeal.pullback (m := m) f A) (GermIdeal.pullback (m := m) f B) := by
  intro y hy G hG
  refine IsInSpanOnAt.trans ?_ (IsInSpanAt.restrict (GermIdeal.mem_pullback_iff.mp hG))
  rintro s ⟨a,ha,rfl⟩
  obtain ⟨K,b,d,hb,hd,hsum⟩ := hAB (f y) (hWV y hy) a ha
  have hfy : ∀ᶠ z in 𝓝 y,ContMDiffAt 𝓘(ℂ,ComplexModel m) 𝓘(ℂ,ComplexModel n) ∞ f z :=
    Eventually.of_forall fun _ => hf.contMDiffAt
  refine ⟨K,fun i => b i ∘ f,fun i => d i ∘ f,fun i => ?_,
    fun i => (hd i).comp_contMDiff hfy,?_⟩
  · exact GermIdeal.mem_pullback_iff.mpr
      (isInSpanAt_self ⟨b i,hb i,rfl⟩
        ((GermIdeal.IsCoherent.holomorphicAt_mem hB (hb i)).comp_contMDiff hfy))
  · filter_upwards [hf.continuous.continuousAt.eventually hsum] with z hz hzW
    exact hz (hWV z hzW)

/-- Actual projection-plus-horizontal transports current SOURCE whole
normalization on the proper carrier, with full E and original scaled mark. -/
theorem projection_power_normalization (M : MarkedIdeal n X) {k : ℕ} (hM : IsInvDomain k M)
    (J : GermIdeal n X) (hJ : J.IsCoherent) (e : ℕ)
    (hLe : RestrictLe M.N J (idealPow M.ideal e))
    (hGe : RestrictLe M.N (idealPow M.ideal e) J) :
    let R : MarkedIdeal n X := ⟨M.N,M.E,J,M.d*e⟩
    RestrictEquiv (projectionTest R) (powerMarked (projectionTest M) e) := by
  dsimp only
  have hf : ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞
      (Prod.fst : projectionAmbient X → X) :=
    contMDiff_fst (n := n) (m := 1) (X := X) (Y := ComplexModel 1)
  have hp := HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow
    (f := (Prod.fst : projectionAmbient X → X)) hf hM.isWellFormed.isCoherent e
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · change RestrictLe (Prod.fst ⁻¹' M.N)
      (GermIdeal.pullback (m := n+1) Prod.fst J)
      (idealPow (GermIdeal.pullback (m := n+1) Prod.fst M.ideal) e)
    rw [←hp]
    exact cross_dimension_restrictLe_pullback
      (Y := projectionAmbient X) (f := (Prod.fst : projectionAmbient X → X)) hf (fun _ hy => hy)
      (isCoherent_idealPow hM.isWellFormed.isCoherent e) hLe
  · change RestrictLe (Prod.fst ⁻¹' M.N)
      (idealPow (GermIdeal.pullback (m := n+1) Prod.fst M.ideal) e)
      (GermIdeal.pullback (m := n+1) Prod.fst J)
    rw [←hp]
    exact cross_dimension_restrictLe_pullback
      (Y := projectionAmbient X) (f := (Prod.fst : projectionAmbient X → X)) hf (fun _ hy => hy) hJ hGe

/-- Actual ordinary exceptional pullback transports current SOURCE whole
normalization, without centre containment, source testhood or etaleness. -/
theorem exceptional_power_normalization (M : MarkedIdeal n X) {k : ℕ} (hM : IsInvDomain k M)
    (J : GermIdeal n X) (hJ : J.IsCoherent) (e : ℕ)
    (hLe : RestrictLe M.N J (idealPow M.ideal e))
    (hGe : RestrictLe M.N (idealPow M.ideal e) J)
    (i j : Fin M.E.length) {Y : CMfd.{u} n} {π : Y → X}
    (hπ : IsBlowupAlong n (M.E.get i ∩ M.E.get j) π) :
    let R : MarkedIdeal n X := ⟨M.N,M.E,J,M.d*e⟩
    RestrictEquiv (exceptionalTest R i j π) (powerMarked (exceptionalTest M i j π) e) := by
  dsimp only
  have hWV : ∀ y ∈ geoStrictTransform π (M.E.get i ∩ M.E.get j) M.N,π y ∈ M.N :=
    fun _ hy => geoStrictTransform_subset_preimage hπ.contMDiff.continuous
      hM.isWellFormed.isClosedSubmanifold_N.1 hy
  have hp := HironakaSmoothSubmersionCoefficientIdeals.pullback_idealPow
    hπ.contMDiff hM.isWellFormed.isCoherent e
  refine ⟨rfl,rfl,rfl,?_,?_⟩
  · change RestrictLe (geoStrictTransform π (M.E.get i ∩ M.E.get j) M.N)
      (GermIdeal.pullback (m := n) π J) (idealPow (GermIdeal.pullback (m := n) π M.ideal) e)
    rw [←hp]
    exact cross_dimension_restrictLe_pullback (f := π) hπ.contMDiff hWV
      (isCoherent_idealPow hM.isWellFormed.isCoherent e) hLe
  · change RestrictLe (geoStrictTransform π (M.E.get i ∩ M.E.get j) M.N)
      (idealPow (GermIdeal.pullback (m := n) π M.ideal) e) (GermIdeal.pullback (m := n) π J)
    rw [←hp]
    exact cross_dimension_restrictLe_pullback (f := π) hπ.contMDiff hWV hJ hGe

end
end Hironaka.HironakaActualMixedPullbackNormalization
