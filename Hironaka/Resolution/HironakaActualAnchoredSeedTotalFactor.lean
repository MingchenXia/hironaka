import Hironaka.Resolution.HironakaActualAnchoredVerticalChart
import Hironaka.Resolution.HironakaActualTowerExceptionalAppend

/-! The whole TOTAL-created factor of one fixed first native birth and every
GIVEN primitive anchored tail. No proper-carrier order or future history.
Blueprint FIRST: `hironaka-actual-anchored-seed-total-factor.tex`. -/

set_option autoImplicit false

open Set Filter Classical
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaActualAnchoredSeedTotalFactor

open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec RelativePrincipalizationSpan IdealWeightPowers
  HironakaActualAnchoredVerticalChart HironakaActualInheritedVerticalTotalFactor
  HironakaActualProjectionTestRecord HironakaActualProjectionVerticalBlowupChart
  HironakaActualTowerExceptionalAppend HironakaSharpOriginalMemberProduct
  HironakaSharpActualProductNewExceptionalFactor

open scoped ProductComplexManifold

noncomputable section

private theorem chart_smooth {r : ℕ} {X : CMfd.{u} r}
    (e : OpenPartialHomeomorph X (ComplexModel r))
    (he : e∈atlas (ComplexModel r) X) :
    ∀ z∈e.source, ContMDiffAt 𝓘(ℂ,ComplexModel r) 𝓘(ℂ,ComplexModel r) ∞ e z := by
  have hmax := IsManifold.subset_maximalAtlas (I:=𝓘(ℂ,ComplexModel r)) (n:=∞) he
  intro z hz
  exact (contMDiffOn_of_mem_maximalAtlas hmax).contMDiffAt (e.open_source.mem_nhds hz)

private theorem coordinate_holomorphic {r : ℕ} {X : CMfd.{u} r}
    (e : OpenPartialHomeomorph X (ComplexModel r))
    (he : e∈atlas (ComplexModel r) X) (j : Fin r) {z : X} (hz : z∈e.source) :
    HolomorphicAt r (fun v=>e v j) z := by
  filter_upwards [e.open_source.mem_nhds hz] with v hv
  exact ((EuclideanSpace.proj j : ComplexModel r →L[ℂ] ℂ).differentiableAt.mdifferentiableAt).comp v
    ((chart_smooth e he v hv).mdifferentiableAt (by simp))

/-- The caller's SAME actual first chart is retained before every given tail
and every whole member/power query. All first and tail factors are derived. -/
theorem anchored_seed_total_factor {n : ℕ} {X : CMfd.{u} (n+1)}
    {C : Set X} [Fact (IsClosedSubmanifold (n+1) C)]
    (c : FlatChart (n+1) C)
    (hπ : IsBlowupAlong (n+1) C (blowupProj (n+1) C))
    (hj : c.j=Fin.last n) :
    let Y1 : CMfd.{u} (n+1) := CMfd.of (BlowupSpace (n+1) C)
    let A : BlowupTower X Y1 :=
      BlowupTower.step (BlowupTower.refl : BlowupTower X X)
        C (blowupProj (n+1) C) hπ
    ∀ {Z : CMfd.{u} (n+1)} (R : BlowupTower Y1 Z)
      (e : OpenPartialHomeomorph Z (ComplexModel (n+1))),
      AnchoredInheritedLastChartChain c.homeo R e →
      ∀ z∈e.source,
        (∀ g : Z→ℂ,
          (BlowupTowerTransforms.exceptionalDivisor (A.append R)).ideal.mem z g ↔
            IsInSpanAt (n:=n+1)
              (·=fun v=>e v (Fin.last n)^(R.length+1)) z g) ∧
        (∀ (d : ℕ) (g : Z→ℂ),
          (idealPow (BlowupTowerTransforms.exceptionalDivisor (A.append R)).ideal d).mem z g ↔
            IsInSpanAt (n:=n+1)
              (·=fun v=>e v (Fin.last n)^((R.length+1)*d)) z g) := by
  dsimp only
  let Y1 : CMfd.{u} (n+1) := CMfd.of (BlowupSpace (n+1) C)
  let A : BlowupTower X Y1 :=
    BlowupTower.step (BlowupTower.refl : BlowupTower X X)
      C (blowupProj (n+1) C) hπ
  have hAtlas : c.homeo∈atlas (ComplexModel (n+1)) Y1 :=
    atlasHomeo_mem_atlas c.toPartialEquiv (Or.inl ⟨c,rfl⟩)
  have hSmooth : ∀ z∈c.source,
      ContMDiffAt 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel (n+1)) ∞ c.toFun z := by
    intro z hz
    exact chart_smooth (X:=Y1) c.homeo hAtlas z hz
  have hBorn : BlowupFunctionTransform.IsLocalEquation hπ c.source
      (fun v=>c.toFun v (Fin.last n)) := by
    simpa only [hj] using GlueingTrivialAction.isLocalEquation_monomial (X:=X) (Y:=Y1) hπ
      c.hsrc c.hflat c.hj c.isOpen_source (W:=c.toFun) hSmooth
      (fun v hv=>⟨hv.1,c.monomial_toFun hv⟩)
  have hFirst : (BlowupTowerTransforms.exceptionalDivisor A).ideal =
      (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal := by
    change (GermIdeal.pullback (m:=n+1) (blowupProj (n+1) C)
      (IdealWeightPowers.unitIdeal (n+1) X)).mul
        (BlowupExceptionalDivisor.exceptionalDivisor hπ).ideal = _
    rw [BlowupExceptionalDivisor.pullback_unitIdeal]
    exact BlowupControlledTransform.unitIdeal_mul
      (BlowupExceptionalDivisor.isCoherent_ideal
        (BlowupExceptionalDivisor.exceptionalDivisor hπ))
  intro Z R e h z hz
  have hChain := anchored_chain_to_unanchored c.homeo R e h
  have he : e∈atlas (ComplexModel (n+1)) Z := by
    cases R with
    | refl => exact hChain
    | step R C π hπ => exact hChain.1
  have hτ := coordinate_holomorphic e he (Fin.last n) hz
  have hImage := anchored_chart_projection c.homeo R e h z hz
  have hPull (g : Z→ℂ) :
      (GermIdeal.pullback (m:=n+1) R.proj
        (BlowupTowerTransforms.exceptionalDivisor A).ideal).mem z g ↔
        IsInSpanAt (n:=n+1) (·=fun v=>e v (Fin.last n)) z g := by
    have hgen (f : Y1→ℂ) :
        (BlowupTowerTransforms.exceptionalDivisor A).ideal.mem (R.proj z) f ↔
          IsInSpanAt (n:=n+1) (·=fun v=>c.toFun v (Fin.last n)) (R.proj z) f := by
      rw [hFirst]
      exact hBorn.generates (R.proj z) hImage.1 f
    have hh := MemberPullback.pullback_mem_iff_of_generator R.contMDiff_proj
      (hBorn.holomorphicAt hImage.1) hgen g
    apply hh.trans
    apply MemberPullback.isInSpanAt_eq_congr
    filter_upwards [e.open_source.mem_nhds hz] with v hv
    exact (anchored_chart_projection c.homeo R e h v hv).2.2.2
  have hTotal (g : Z→ℂ) :
      (BlowupTowerTransforms.exceptionalDivisor (A.append R)).ideal.mem z g ↔
        IsInSpanAt (n:=n+1) (·=fun v=>e v (Fin.last n)^(R.length+1)) z g := by
    rw [exceptionalDivisor_append_ideal A R]
    have hh := mul_mem_iff_principal hτ (BlowupDerivativeIdeal.holomorphicAt_pow hτ R.length)
      hPull (inherited_total_divisor_mem_iff R e hChain z hz) g
    have hfun : (fun v=>e v (Fin.last n))*(fun v=>e v (Fin.last n)^R.length)=
        (fun v=>e v (Fin.last n)^(R.length+1)) := by
      funext v
      simp only [Pi.mul_apply,pow_succ,mul_comm]
    rwa [hfun] at hh
  refine ⟨hTotal,?_⟩
  intro d g
  have hh := idealPow_principal_mem_iff
    (BlowupDerivativeIdeal.holomorphicAt_pow hτ (R.length+1)) hTotal d g
  have hfun : (fun v=>e v (Fin.last n)^(R.length+1))^d=
      (fun v=>e v (Fin.last n)^((R.length+1)*d)) := by
    funext v
    exact (pow_mul _ _ _).symm
  rwa [hfun] at hh

/-- Only ordinary original inputs choose one first native chart, before ALL
given anchored tails and arbitrary whole ideal/power queries. -/
theorem exists_original_anchored_seed_total_factor
    {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M)
    (x : X) (hx : x∈M.cosupp) :
    let p : projectionAmbient X := (x,0)
    let C : Set (projectionAmbient X) := {p}
    let _ : Fact (IsClosedSubmanifold (n+1) C) :=
      ⟨(projection_point_centre M hM x hx).1.1⟩
    let X0 : CMfd.{u} (n+1) := CMfd.of (projectionAmbient X)
    let Y1 : CMfd.{u} (n+1) := CMfd.of (BlowupSpace (n+1) C)
    let π : Y1→X0 := blowupProj (n+1) C
    ∃ (c : FlatChart (n+1) C) (hπ : IsBlowupAlong (n+1) C π),
      c.y₀=p ∧ c.k=0 ∧ c.j=Fin.last n ∧
      (∀ y : projectionAmbient X, flatCoord c.Φ (Fin.last n) y=y.2 0) ∧
      c.homeo∈atlas (ComplexModel (n+1)) Y1 ∧
      (0 : ComplexModel (n+1))∈c.target ∧
      c.invFun 0∈c.source ∧ π (c.invFun 0)=p ∧ c.toFun (c.invFun 0)=0 ∧
      let A : BlowupTower X0 Y1 :=
        BlowupTower.step (BlowupTower.refl : BlowupTower X0 X0) C π hπ
      ∀ {Z : CMfd.{u} (n+1)} (R : BlowupTower Y1 Z)
        (e : OpenPartialHomeomorph Z (ComplexModel (n+1))),
        AnchoredInheritedLastChartChain c.homeo R e →
        ∀ z∈e.source,
          (∀ g : Z→ℂ,
            (BlowupTowerTransforms.exceptionalDivisor (A.append R)).ideal.mem z g ↔
              IsInSpanAt (n:=n+1)
                (·=fun v=>e v (Fin.last n)^(R.length+1)) z g) ∧
          (∀ (d : ℕ) (g : Z→ℂ),
            (idealPow (BlowupTowerTransforms.exceptionalDivisor (A.append R)).ideal d).mem z g ↔
              IsInSpanAt (n:=n+1)
                (·=fun v=>e v (Fin.last n)^((R.length+1)*d)) z g) := by
  dsimp only
  let p : projectionAmbient X := (x,0)
  let C : Set (projectionAmbient X) := {p}
  let _ : Fact (IsClosedSubmanifold (n+1) C) :=
    ⟨(projection_point_centre M hM x hx).1.1⟩
  let X0 : CMfd.{u} (n+1) := CMfd.of (projectionAmbient X)
  obtain ⟨Φ,c,SN,SE,U,h⟩ := exists_original_anchored_vertical_frame M hM x hx
  rcases h with ⟨_hΦs,_hΦ0,hcp,hck,hcj,_hOld,hLast,_hSourceN,_hSourceE,
    _hSN,_hSE,h0c,hzSource,hzp,hWz,hπ,hAtlas,_⟩
  refine ⟨c,hπ,hcp,hck,hcj,hLast,hAtlas,h0c,hzSource,hzp,hWz,?_⟩
  exact anchored_seed_total_factor (X:=X0) (C:=C) c hπ hcj

end

end Hironaka.HironakaActualAnchoredSeedTotalFactor
