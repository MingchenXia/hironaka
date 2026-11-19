import Hironaka.Resolution.HironakaActualFixedFlatteningHSComparison
import Hironaka.Resolution.HironakaActualGivenFlatteningBlowupSquare
import Hironaka.Resolution.HironakaActualAnalyticOwnerPermutationQuotient
import Hironaka.Resolution.HironakaActualHistoricalMovingCentreChart

/-! Native geometric squares and ENTIRE strict/profile transport for the
SAME given flattening in literal original selected indices. No family,
monicity, target chart or desired square is supplied to the native producer. -/
set_option autoImplicit false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
universe u
namespace Hironaka.HironakaActualSelectedFlatteningHSComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupFlatCoordinates HironakaHolomorphicJetChartInvariance
  HironakaActualFlatCoordinateIntrinsicHS HironakaActualVanishingIntrinsicHSTransport
  HironakaActualOpenCoordinateStrictSquare HironakaActualAnalyticBlowupTaylor
  HironakaActualFixedFlatteningHSComparison HironakaActualGivenFlatteningBlowupSquare
  HironakaActualAnalyticOwnerPermutationQuotient HironakaActualFixedInheritedSelectorPermutation
  HironakaActualHistoricalMovingCentreChart
  HironakaSmoothCentreCoherentDomain
  HironakaActualPointGeometricBennett HironakaRelativeNormalDeformationInitialRelations

variable {n : ℕ} {X Y : Type u}
  [TopologicalSpace X] [ChartedSpace (ComplexModel n) X] [IsComplexManifold n X]
  [TopologicalSpace Y] [ChartedSpace (ComplexModel n) Y] [IsComplexManifold n Y]

/-- The ENTIRE true native strict set commutes with the actual selected
polynomial square, with ANY literal original normal subset. -/
theorem strictTransform_eq_selectedFlattening_preimage {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π) (z : Y) (A : Set (Fin n))
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π z) (π z)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (π z)).target)
    (j : Fin n) (b : Fin n → ℂ)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) z z))
    (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) z).target)
    (hnormal : ∀ y : Y, y ∈ (chartAt (ComplexModel n) z).source →
      chartAt (ComplexModel n) z y ∈ Θ.source →
      π y ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=
        actualAnalyticBlowupMap A j b (Θ.toFun (chartAt (ComplexModel n) z y)))
    (W : Set X) :
    let U : Opens (ComplexModel n) := ⟨Θ.target,Θ.isOpen_target⟩
    (fun q : U => actualFlatteningInverseMap z Θ q) ⁻¹' strictTransform n π W=
      (Subtype.val : U → ComplexModel n) ⁻¹'
        strictTransform n (actualAnalyticBlowupMap A j b)
          (actualFixedFlatteningSet (π z) Φ W) := by
  let DX : Opens X := ⟨flatDomain Φ,isOpen_flatDomain Φ⟩
  let DY : Opens Y := ⟨flatDomain Θ,isOpen_flatDomain Θ⟩
  let V : Opens (ComplexModel n) := ⟨Φ.target,Φ.isOpen_target⟩
  let U : Opens (ComplexModel n) := ⟨Θ.target,Θ.isOpen_target⟩
  let a : V ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ DX :=
    (actualFlatCoordinateDiffeomorph Φ hΦsrc).symm
  let c : U ≃ₘ⟮𝓘(ℂ,ComplexModel n),𝓘(ℂ,ComplexModel n)⟯ DY :=
    (actualFlatCoordinateDiffeomorph Θ hΘsrc).symm
  let P := actualAnalyticBlowupMap A j b
  have hnorm (q : U) : π (c q : Y) ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π z) (π (c q : Y)))=P q := by
    have hy := (c q).2
    have h := hnormal (c q) hy.1 hy.2
    have hc : Θ.toFun (chartAt (ComplexModel n) z (c q : Y))=(q : ComplexModel n) :=
      (flatInverse_mem Θ q.2 hΘsrc).2
    rw [hc] at h
    exact h
  have hPinto (q : U) : P q ∈ V := by
    change P q ∈ Φ.target
    rw [← (hnorm q).2]
    exact Φ.mapsTo_toFun (hnorm q).1.2
  let Q : U → V := fun q => ⟨P q,hPinto q⟩
  have hP : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ P := by
    intro q
    apply MarkedIdealOpenBiholomorphism.contMDiffAt_of_eventually_mdifferentiableAt'
    exact Eventually.of_forall fun _ =>
      (differentiable_actualAnalyticBlowupMap A j b).differentiableAt.mdifferentiableAt
  have hQ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ Q :=
    BlowupRestrictOpen.contMDiff_opens_mk (hP.comp contMDiff_subtype_val) hPinto
  have hcomm (q : U) : π (c q : Y)=(a (Q q) : X) := by
    change π (c q : Y)=(chartAt (ComplexModel n) (π z)).symm (Φ.invFun (P q))
    rw [← (hnorm q).2]
    exact (flatInverse_flat Φ (hnorm q).1).symm
  have hA : (Subtype.val : V → ComplexModel n) ⁻¹' actualFixedFlatteningSet (π z) Φ W=
      (fun q : V => (a q : X)) ⁻¹' W := by
    ext q
    exact and_iff_right q.2
  have hglobal := strictTransform_actual_open_coordinate_square π Q hπ hQ DX DY a c hcomm W
  have hmodel := strictTransform_actual_open_coordinate_square P Q hP hQ V U
    (Diffeomorph.refl _ _ _) (Diffeomorph.refl _ _ _) (fun _ => rfl)
      (actualFixedFlatteningSet (π z) Φ W)
  change strictTransform n Q ((Subtype.val : V → ComplexModel n) ⁻¹'
    actualFixedFlatteningSet (π z) Φ W)=
      (Subtype.val : U → ComplexModel n) ⁻¹' strictTransform n P (actualFixedFlatteningSet (π z) Φ W) at hmodel
  rw [hA] at hmodel
  exact hglobal.symm.trans hmodel

/-- Every original strict-transform intrinsic HS value is the same model strict-transform value at zero. -/
theorem hilbertSamuelAt_strict_eq_selectedFlattening_model {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π) (z : Y) (A : Set (Fin n))
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π z) (π z)))
    (hΦsrc : Φ.source ⊆ (chartAt (ComplexModel n) (π z)).target)
    (j : Fin n) (b : Fin n → ℂ)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) z z))
    (hΘsrc : Θ.source ⊆ (chartAt (ComplexModel n) z).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) z z)=0)
    (hnormal : ∀ y : Y, y ∈ (chartAt (ComplexModel n) z).source →
      chartAt (ComplexModel n) z y ∈ Θ.source →
      π y ∈ flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=
        actualAnalyticBlowupMap A j b (Θ.toFun (chartAt (ComplexModel n) z y)))
    (W : Set X) (ℓ : ℕ) :
    hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W)) z ℓ=
      hilbertSamuelAt (vanishingIdeal (n := n)
        (strictTransform n (actualAnalyticBlowupMap A j b)
          (actualFixedFlatteningSet (π z) Φ W))) 0 ℓ := by
  let U : Opens (ComplexModel n) := ⟨Θ.target,Θ.isOpen_target⟩
  have h0U : (0 : ComplexModel n) ∈ U := actualFlattening_target_zero_mem z Θ hΘ0
  let u0 : U := ⟨0,h0U⟩
  have hstrict := strictTransform_eq_selectedFlattening_preimage hπ z A Φ hΦsrc j b Θ hΘsrc hnormal W
  have hleft := hilbertSamuelAt_vanishing_actual_flat_inverse Θ hΘsrc (strictTransform n π W) u0 ℓ
  change hilbertSamuelAt (vanishingIdeal (n := n)
    ((fun q : U => actualFlatteningInverseMap z Θ q) ⁻¹' strictTransform n π W)) u0 ℓ=
      hilbertSamuelAt (vanishingIdeal (n := n) (strictTransform n π W))
        (actualFlatteningInverseMap z Θ 0) ℓ at hleft
  rw [actualFlatteningInverseMap_zero z Θ hΘ0] at hleft
  calc
    _ = hilbertSamuelAt (vanishingIdeal (n := n)
        ((fun q : U => actualFlatteningInverseMap z Θ q) ⁻¹' strictTransform n π W)) u0 ℓ := hleft.symm
    _ = hilbertSamuelAt (vanishingIdeal (n := n)
        ((Subtype.val : U → ComplexModel n) ⁻¹'
          strictTransform n (actualAnalyticBlowupMap A j b)
            (actualFixedFlatteningSet (π z) Φ W))) u0 ℓ := by rw [hstrict]
    _ = _ := hilbertSamuelAt_vanishing_actual_open_any U _ u0 ℓ


private theorem original_vanishing_origin_congr_near_zero
    (S T : Set (ComplexModel n))
    (hST : ∀ᶠz in 𝓝 (0 : ComplexModel n),z∈S ↔ z∈T) :
    originalCoherentOriginIdeal (vanishingIdeal (n:=n) S)=
      originalCoherentOriginIdeal (vanishingIdeal (n:=n) T) := by
  ext g
  obtain ⟨G,hG,rfl⟩:=HolGerm.exists_eq_mk g
  rw [mk_mem_original_vanishing_origin_ideal_iff,mk_mem_original_vanishing_origin_ideal_iff]
  constructor
  · intro h
    filter_upwards [h,hST] with z hz hzt hzT
    exact hz (hzt.mpr hzT)
  · intro h
    filter_upwards [h,hST] with z hz hzt hzS
    exact hz (hzt.mp hzS)

/-- The ENTIRE true native strict origin ideal in the SAME actual target
coordinates equals the ENTIRE selected model strict vanishing origin ideal. -/
theorem originalStrictFlattenedOriginIdeal_eq_selected_model {π : Y → X}
    (hπ : ContMDiff 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ∞ π) (z : Y) (A : Set (Fin n))
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π z) (π z)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) (π z)).target)
    (e : Fin n) (b : Fin n → ℂ)
    (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) z z))
    (hΘsrc : Θ.source⊆(chartAt (ComplexModel n) z).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel n) z z)=0)
    (hNormal : ∀y : Y,y∈(chartAt (ComplexModel n) z).source →
      chartAt (ComplexModel n) z y∈Θ.source → π y∈flatDomain Φ ∧
      Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=
        actualAnalyticBlowupMap A e b (Θ.toFun (chartAt (ComplexModel n) z y)))
    (W : Set X) :
    originalCoherentOriginIdeal (HironakaRelativeNormalCoherentTranslatedJets.actualTranslatedOriginalSheaf
      (actualFlattenedOriginalSheaf (vanishingIdeal (n:=n) (strictTransform n π W)) z Θ) 0)=
      originalCoherentOriginIdeal (vanishingIdeal (n:=n) (strictTransform n
        (actualAnalyticBlowupMap A e b) (actualFixedFlatteningSet (π z) Φ W))) := by
  rw [originalFlattenedVanishingOriginIdeal_eq_model z Θ hΘsrc hΘ0]
  apply original_vanishing_origin_congr_near_zero
  let U : Opens (ComplexModel n):=⟨Θ.target,Θ.isOpen_target⟩
  have h0 : (0 : ComplexModel n)∈Θ.target:=actualFlattening_target_zero_mem z Θ hΘ0
  have hStrict:=strictTransform_eq_selectedFlattening_preimage hπ z A Φ hΦsrc e b Θ hΘsrc hNormal W
  filter_upwards [Θ.isOpen_target.mem_nhds h0] with u hu
  have h : (actualFlatteningInverseMap z Θ u∈strictTransform n π W) ↔
      u∈strictTransform n (actualAnalyticBlowupMap A e b) (actualFixedFlatteningSet (π z) Φ W) :=
    Iff.of_eq (congrArg (fun S : Set U=>(⟨u,hu⟩ : U)∈S) hStrict)
  exact (and_iff_right hu).trans h

private def outputLinearChart {c : ComplexModel n} (R : ComplexModel n ≃L[ℂ] ComplexModel n)
    (Φ : LocalHolomorphicEquivAt (n:=n) c) : LocalHolomorphicEquivAt (n:=n) c where
  source:=Φ.source
  target:=R ⁻¹' Φ.target
  isOpen_source:=Φ.isOpen_source
  isOpen_target:=Φ.isOpen_target.preimage R.continuous
  center_mem_source:=Φ.center_mem_source
  toFun:=R.symm ∘ Φ.toFun
  invFun:=Φ.invFun ∘ R
  toFun_holomorphic:=R.symm.differentiable.comp_differentiableOn Φ.toFun_holomorphic
  invFun_holomorphic:=Φ.invFun_holomorphic.comp R.differentiable.differentiableOn (fun _ hz=>hz)
  mapsTo_toFun:=by
    intro z hz
    change R (R.symm (Φ.toFun z))∈Φ.target
    rw [R.apply_symm_apply]
    exact Φ.mapsTo_toFun hz
  mapsTo_invFun:=fun _ hz=>Φ.mapsTo_invFun hz
  left_inv:=by
    intro z hz
    change Φ.invFun (R (R.symm (Φ.toFun z)))=z
    rw [R.apply_symm_apply,Φ.left_inv z hz]
  right_inv:=by
    intro z hz
    change R.symm (Φ.toFun (Φ.invFun (R z)))=z
    rw [Φ.right_inv (R z) hz,R.symm_apply_apply]

/-- A genuine native blowup internally constructs the whole polynomial
square in the SAME given source flattening and ORIGINAL selected indices.
The priority permutation is used only for native geometry, never for a family. -/
theorem exists_actual_given_selected_flattening_blowup_square
    {C : Set X} {π : Y → X} (hπ : IsBlowupAlong n C π) (z : Y)
    (k : ℕ) (p : Fin n ≃ Fin n)
    (Φ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) (π z) (π z)))
    (hΦsrc : Φ.source⊆(chartAt (ComplexModel n) (π z)).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) (π z) (π z))=0)
    (hFlat : ∀{x : X},x∈(chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) x∈Φ.source →
        (x∈C ↔ Φ.toFun (chartAt (ComplexModel n) (π z) x)∈
          coordinateSubsetPlane {i : Fin n | k≤(p i).val})) :
    ∃e : Fin n,k≤(p e).val ∧ ∃(b : Fin n → ℂ)
      (Θ : LocalHolomorphicEquivAt (chartAt (ComplexModel n) z z)),
      (∀i : Fin n,(p i).val<k → b i=0) ∧ b e=0 ∧
      (∀i : Fin n,k≤(p i).val → i≠e → ‖b i‖≤1) ∧
      Θ.source⊆(chartAt (ComplexModel n) z).target ∧
      Θ.toFun (chartAt (ComplexModel n) z z)=0 ∧
      (∀y : Y,y∈(chartAt (ComplexModel n) z).source →
        chartAt (ComplexModel n) z y∈Θ.source →
        π y∈flatDomain Φ ∧
          Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=
            actualAnalyticBlowupMap {i : Fin n | k≤(p i).val} e b
              (Θ.toFun (chartAt (ComplexModel n) z y))) ∧
      ∀(W : Set X)(ℓ : ℕ),hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n π W)) z ℓ=
        hilbertSamuelAt (vanishingIdeal (n:=n) (strictTransform n
          (actualAnalyticBlowupMap {i : Fin n | k≤(p i).val} e b)
          (actualFixedFlatteningSet (π z) Φ W))) 0 ℓ := by
  let R:=actualPermutationLinearEquiv p
  let Ω:=outputLinearChart R Φ
  have hΩ0 : Ω.toFun (chartAt (ComplexModel n) (π z) (π z))=0 := by
    change R.symm (Φ.toFun (chartAt (ComplexModel n) (π z) (π z)))=0
    rw [hΦ0,map_zero]
  have hFlatΩ : ∀{x : X},x∈(chartAt (ComplexModel n) (π z)).source →
      chartAt (ComplexModel n) (π z) x∈Ω.source →
      (x∈C ↔ Ω.toFun (chartAt (ComplexModel n) (π z) x)∈complexCoordinatePlane n k) := by
    intro x hx hxΦ
    exact (hFlat hx hxΦ).trans
      (coordinateSubsetPlane_permutation p k (Φ.toFun (chartAt (ComplexModel n) (π z) x))).symm
  obtain ⟨j,hj,bT,ΘT,hbT,hbj,hBound,hΘsrc,hΘ0,hNormalT⟩:=
    exists_actual_given_flattening_blowup_square hπ (π z) z rfl k Ω hΦsrc hΩ0 hFlatΩ
  let A : Set (Fin n):={i | k≤(p i).val}
  let e:=p.symm j
  let b : Fin n → ℂ:=fun i=>bT (p i)
  let Θ:=outputLinearChart R.symm ΘT
  have hpe : p e=j:=p.apply_symm_apply j
  have hImage : p '' A={i : Fin n | k ≤ i.val} := by
    ext i
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hi
      refine ⟨p.symm i,?_,p.apply_symm_apply i⟩
      change k≤(p (p.symm i)).val
      simpa only [p.apply_symm_apply,Set.mem_ofPred_eq] using hi
  have hbConjugate : (fun i=>b (p.symm i))=bT := by
    funext i
    exact congrArg bT (p.apply_symm_apply i)
  have hΘOriginal0 : Θ.toFun (chartAt (ComplexModel n) z z)=0 := by
    change R (ΘT.toFun (chartAt (ComplexModel n) z z))=0
    rw [hΘ0,map_zero]
  have hNormal : ∀y : Y,y∈(chartAt (ComplexModel n) z).source →
      chartAt (ComplexModel n) z y∈Θ.source →
      π y∈flatDomain Φ ∧
        Φ.toFun (chartAt (ComplexModel n) (π z) (π y))=
          actualAnalyticBlowupMap A e b (Θ.toFun (chartAt (ComplexModel n) z y)) := by
    intro y hy hyΘ
    have hT:=hNormalT y hy hyΘ
    refine ⟨hT.1,?_⟩
    have hEq:=congrArg R hT.2
    change R (R.symm (Φ.toFun (chartAt (ComplexModel n) (π z) (π y))))=
      R (actualAnalyticBlowupMap {i : Fin n | k ≤ i.val} j bT
        (ΘT.toFun (chartAt (ComplexModel n) z y))) at hEq
    rw [R.apply_symm_apply] at hEq
    have hPerm:=actualAnalyticBlowupMap_permutation_square p A e b
      (ΘT.toFun (chartAt (ComplexModel n) z y))
    rw [hImage,hpe,hbConjugate] at hPerm
    exact hEq.trans hPerm
  refine ⟨e,by simpa only [hpe] using hj,b,Θ,?_,?_,?_,hΘsrc,hΘOriginal0,hNormal,?_⟩
  · intro i hi
    exact hbT (p i) hi
  · change bT (p e)=0
    rw [hpe]
    exact hbj
  · intro i hi hie
    exact hBound (p i) hi (by intro h;apply hie;apply p.injective;exact h.trans hpe.symm)
  · intro W ℓ
    exact hilbertSamuelAt_strict_eq_selectedFlattening_model hπ.contMDiff z A Φ hΦsrc e b Θ
      hΘsrc hΘOriginal0 hNormal W ℓ

end
end Hironaka.HironakaActualSelectedFlatteningHSComparison
