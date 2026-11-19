import Hironaka.Resolution.HironakaActualAnchoredStrictCarrierMask
import Hironaka.Resolution.HironakaActualIteratedVerticalTaylor
import Hironaka.Resolution.HironakaActualInheritedVerticalPointChart
import Hironaka.Manifold.LocalHolomorphicInverse

/-! The SAME original frame is restricted before all queries. The actual
proper-mask inverse square is derived only on its internally derived window.
No incoming germ/order/factor/test/cosupport packet, or private parent call. -/
set_option autoImplicit false
open Set Filter Classical
open scoped Topology Manifold ContDiff BigOperators
universe u
namespace Hironaka.HironakaActualAnchoredOriginalGermSquare
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  BlowupTowers BlowupConstruction BlowupFlatCoordinates BlowupMonomialCharts
  BlowupStrictSubmanifold NormalCrossings MarkedIdeals MarkedIdeals.MarkedIdeal
  ResolutionInvariantSpec GiraudAlong ExceptionalPushforwardAlong
  HironakaActualProjectionTestRecord HironakaActualProjectionVerticalBlowupChart
  HironakaActualProjectionVerticalFunctionOrder HironakaActualInheritedVerticalPointChart
  HironakaActualAnchoredVerticalChart HironakaActualAnchoredStrictCarrierMask
  HironakaActualIteratedVerticalTaylor HironakaActualAnalyticBlowupTaylor
  HironakaRelativeNormalIdeal HironakaHolomorphicPointJets IdealWeightPowers
  HironakaActualOriginalFormalTaylor GermIdealOrder HironakaRelativeNormalMonomialBasis
  HironakaActualCoefficientPresentationCentrePower
open scoped ProductComplexManifold

private def oldMask {n : ℕ} (S : Finset (Fin (n+1))) : Finset (Fin n) :=
  Finset.univ.filter fun i=>i.castAdd 1∈S

private theorem mask_membership {n : ℕ} (S : Finset (Fin (n+1)))
    (v : ComplexModel (n+1)) (a : ComplexModel n)
    (hOld : ∀i : Fin n,v (i.castAdd 1)=a i) (hLast : v (Fin.last n)=0) :
    v∈coordSubspace S ↔ a∈coordSubspace (oldMask S) := by
  constructor
  · intro h i hi
    rw [←hOld i]
    exact h (i.castAdd 1) (by simpa only [oldMask,Finset.mem_filter,Finset.mem_univ,true_and] using hi)
  · intro h j hj
    by_cases he : j=Fin.last n
    · rw [he];exact hLast
    · have hjn : j.val<n := by
        have hneq : j.val≠n:=fun hh=>he (Fin.ext hh)
        have hjlt:=j.isLt
        omega
      let i : Fin n:=⟨j.val,hjn⟩
      have hij : i.castAdd 1=j:=Fin.ext rfl
      rw [←hij,hOld]
      apply h
      simpa only [oldMask,Finset.mem_filter,Finset.mem_univ,true_and,hij] using hj

/-- Derive the source shrink from the zero section; the original forward and
inverse functions are unchanged. No original n-variable shrink or mask is supplied. -/
theorem source_mask_restriction {n : ℕ} {X : CMfd.{u} n}
    (N : Set X) (x : X)
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (hΦs : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    {C : Set (projectionAmbient X)} [Fact (IsClosedSubmanifold (n+1) C)]
    (c : FlatChart (n+1) C) (hcp : c.y₀=(x,0)) (SN : Finset (Fin (n+1)))
    (hOld : ∀(y : projectionAmbient X)(i : Fin n),
      flatCoord c.Φ (i.castAdd 1) y=flatCoord Φ i y.1)
    (hLast : ∀y : projectionAmbient X,flatCoord c.Φ (Fin.last n) y=y.2 0)
    (hSourceN : ∀y∈flatDomain c.Φ,
      y∈(Prod.fst : projectionAmbient X→X) ⁻¹' N ↔
      c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀ y)∈coordSubspace SN) :
    ∃Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x),
      Φs.toFun=Φ.toFun ∧ Φs.invFun=Φ.invFun ∧
      Φs.source⊆Φ.source ∧ Φs.target⊆Φ.target ∧
      Φs.source⊆(chartAt (ComplexModel n) x).target ∧
      Φs.toFun (chartAt (ComplexModel n) x x)=0 ∧
      flatDomain Φs=flatDomain Φ∩
        (fun y : X=>((y,0) : projectionAmbient X)) ⁻¹' flatDomain c.Φ ∧
      ∀y∈flatDomain Φs,y∈N ↔ flatMap Φs y∈coordSubspace (oldMask SN) := by
  let σ : X→projectionAmbient X:=fun y=>(y,0)
  let D : Set X:=flatDomain Φ∩σ ⁻¹' flatDomain c.Φ
  have hσ : Continuous σ:=continuous_id.prodMk continuous_const
  have hD : IsOpen D:=(isOpen_flatDomain Φ).inter ((isOpen_flatDomain c.Φ).preimage hσ)
  have hxD : x∈D:=⟨mem_flatDomain_self Φ,by
    change (x,0)∈flatDomain c.Φ
    rw [←hcp]
    exact mem_flatDomain_self c.Φ⟩
  let a:=chartAt (ComplexModel n) x
  let B : Set (ComplexModel n):=a.target∩a.symm ⁻¹' D
  have hB : IsOpen B:=a.isOpen_inter_preimage_symm hD
  have hCent : a x∈Φ.source∩B:=⟨Φ.center_mem_source,
    a.map_source (mem_chart_source _ x),by
      change a.symm (a x)∈D
      rw [a.left_inv (mem_chart_source _ x)]
      exact hxD⟩
  let Φs:=Φ.restrict B hB (a x) hCent
  have hDom : flatDomain Φs=D := by
    ext y
    constructor
    · intro hy
      have hInv : a.symm (a y)∈D:=hy.2.2.2
      rwa [a.left_inv hy.1] at hInv
    · intro hy
      exact ⟨hy.1.1,hy.1.2,a.map_source hy.1.1,by
        change a.symm (a y)∈D
        rwa [a.left_inv hy.1.1]⟩
  refine ⟨Φs,rfl,rfl,(fun _ h=>h.1),(fun _ h=>h.1),
    (fun _ h=>hΦs h.1),hΦ0,hDom,?_⟩
  intro y hy
  have hyD : y∈D:=hDom ▸ hy
  have hN:=hSourceN (σ y) hyD.2
  exact hN.trans (mask_membership SN _ (flatMap Φs y)
    (fun i=>hOld (σ y) i) (hLast (σ y)))

private theorem mask_apply {n : ℕ} (S : Finset (Fin n)) (w : ComplexModel n) (j : Fin n) :
    maskRetract S w j=if j∈S then 0 else w j := by
  simp only [maskRetract,_root_.sum_apply,ContinuousLinearMap.smulRight_apply]
  rw [WithLp.ofLp_sum]
  simp only [Finset.sum_apply,WithLp.ofLp_smul,PiLp.single_apply,Pi.smul_apply,smul_eq_mul,
    mul_ite,mul_one,mul_zero,EuclideanSpace.proj,PiLp.proj_apply]
  rw [Finset.sum_ite_eq]
  simp

private theorem mask_base {n : ℕ} (S : Finset (Fin (n+1))) (hS : Fin.last n∉S)
    (q : ℕ) (w : ComplexModel (n+1)) :
    iteratedVerticalBase n q (maskRetract S w)=
      maskRetract (oldMask S) (iteratedVerticalBase n q w) := by
  ext i
  rw [(iterated_vertical_base_coordinates n q (maskRetract S w)).1 i,
    mask_apply S w (Fin.last n),mask_apply S w (i.castAdd 1),
    mask_apply (oldMask S) (iteratedVerticalBase n q w) i,
    (iterated_vertical_base_coordinates n q w).1 i]
  simp only [if_neg hS,oldMask,Finset.mem_filter,Finset.mem_univ,true_and]
  split_ifs <;> simp

private theorem first_vector {n : ℕ} {X : CMfd.{u} n}
    {C : Set (projectionAmbient X)} [Fact (IsClosedSubmanifold (n+1) C)]
    (x : X) (c : FlatChart (n+1) C) (hck : c.k=0) (hcj : c.j=Fin.last n)
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (hOld : ∀(y : projectionAmbient X)(i : Fin n),
      flatCoord c.Φ (i.castAdd 1) y=flatCoord Φ i y.1)
    {Z : CMfd.{u} (n+1)}
    (R : BlowupTower (CMfd.of (BlowupSpace (n+1) C)) Z)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1)))
    (hA : AnchoredInheritedLastChartChain c.homeo R e) :
    ∀v∈e.source,
      flatMap Φ ((blowupProj (n+1) C (R.proj v)).1)=
        iteratedVerticalBase n (R.length+1) (e v) := by
  intro v hv
  have hh:=anchored_chart_projection c.homeo R e hA v hv
  have hm:=c.monomial_toFun hh.1
  simp only [FlatChart.homeo_apply] at hh
  rw [hck,hcj] at hm
  ext i
  have hi : i.castAdd 1≠Fin.last n := by
    intro he
    have heq:=congrArg Fin.val he
    have hlt:=i.isLt
    simp only [Fin.val_castAdd,Fin.val_last] at heq
    omega
  calc
    flatMap Φ ((blowupProj (n+1) C (R.proj v)).1) i=
        flatCoord c.Φ (i.castAdd 1) (blowupProj (n+1) C (R.proj v)) := (hOld _ i).symm
    _=monomial 0 (Fin.last n) (c.toFun (R.proj v)) (i.castAdd 1) :=
      (congrArg (fun w : ComplexModel (n+1)=>w (i.castAdd 1)) hm).symm
    _=iteratedVerticalBase n (R.length+1) (e v) i := by
      rw [(iterated_vertical_base_coordinates n (R.length+1) (e v)).1 i]
      rw [monomial_apply,if_pos ⟨Nat.zero_le _,hi⟩]
      rw [hh.2.2.1 i,hh.2.2.2,pow_succ]
      ring

/-- Actual SOURCE geometry derives current source landing and the POINT-map
inverse square before any original-function query. All inverse use is on W. -/
theorem anchored_original_inverse_square {n : ℕ} {X : CMfd.{u} n}
    (x : X) {C : Set (projectionAmbient X)} [Fact (IsClosedSubmanifold (n+1) C)]
    (c : FlatChart (n+1) C) (hck : c.k=0) (hcj : c.j=Fin.last n)
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (_hΦs : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (_hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (hOld : ∀(y : projectionAmbient X)(i : Fin n),
      flatCoord c.Φ (i.castAdd 1) y=flatCoord Φ i y.1)
    (h0c : (0 : ComplexModel (n+1))∈c.target)
    (hzp : blowupProj (n+1) C (c.invFun 0)=(x,0))
    (Q0 : MarkedIdeal (n+1) (CMfd.of (BlowupSpace (n+1) C)))
    (SN : Finset (Fin (n+1))) (hSN : Fin.last n∉SN)
    (U1 : Set (BlowupSpace (n+1) C)) (hU1 : IsOpen U1)
    (hzU1 : c.invFun 0∈U1) (_hUc : U1⊆c.source)
    (hSourceMask : ∀v∈U1,v∈Q0.N↔c.toFun v∈coordSubspace SN)
    {Z : CMfd.{u} (n+1)}
    (R : BlowupTower (CMfd.of (BlowupSpace (n+1) C)) Z)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1)))
    (hA : AnchoredInheritedLastChartChain c.homeo R e)
    (z : Z) (hz : z∈e.source) (he0 : e z=0) :
    let κ : Z→X := (Prod.fst : projectionAmbient X→X)∘blowupProj (n+1) C∘R.proj
    ∃(W : Set Z)
      (Θ : LocalHolomorphicEquivAt (n:=n+1) (chartAt (ComplexModel (n+1)) z z)),
      κ z=x ∧ W=e.source∩R.proj ⁻¹' (U1∩c.source)∩κ ⁻¹' flatDomain Φ ∧
      IsOpen W ∧ z∈W ∧ W⊆e.source ∧
      Θ.source⊆(chartAt (ComplexModel (n+1)) z).target ∧
      Θ.toFun (chartAt (ComplexModel (n+1)) z z)=0 ∧
      (∀v∈flatDomain Θ,v∈W ∧ flatMap Θ v=e v ∧
        (v∈(Q0.geoTransformAlong R).N↔flatMap Θ v∈coordSubspace SN)) ∧
      (∀v∈W,κ v∈flatDomain Φ ∧
        flatMap Φ (κ v)=iteratedVerticalBase n (R.length+1) (e v)) ∧
      (∀ᶠw in 𝓝 (0 : ComplexModel (n+1)),
        κ (flatInv Θ (maskRetract SN w))=
          flatInv Φ (maskRetract (oldMask SN) (iteratedVerticalBase n (R.length+1) w))) := by
  dsimp only
  let κ : Z→X:=(Prod.fst : projectionAmbient X→X)∘blowupProj (n+1) C∘R.proj
  have hκ : ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞ κ :=
    ((ProductComplexManifold.contMDiff_fst (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1)).comp
      contMDiff_blowupProj).comp R.contMDiff_proj
  have hSeedSource : c.invFun 0∈c.homeo.source:=c.map_target h0c
  have hSeedZero : c.homeo (c.invFun 0)=0:=c.right_inv h0c
  have hO:=anchored_origin_preimage_window c.homeo R e hA (c.invFun 0)
    hSeedSource hSeedZero z hz he0 U1 hU1 hzU1
  have hκz : κ z=x := by
    change (blowupProj (n+1) C (R.proj z)).1=x
    rw [hO.1,hzp]
  have hV:=anchored_strict_carrier_mask Q0 c.homeo (c.invFun 0) hSeedSource hSeedZero
    U1 hU1 hzU1 SN hSN (fun v hv=>hSourceMask v hv.1) R e hA
  let V : Set Z:=e.source∩R.proj ⁻¹' (U1∩c.source)
  let W : Set Z:=V∩κ ⁻¹' flatDomain Φ
  have hW : IsOpen W:=hV.1.inter ((isOpen_flatDomain Φ).preimage hκ.continuous)
  have hzW : z∈W:=⟨(hV.2.2 z hz he0).1,by
    change κ z∈flatDomain Φ
    rw [hκz]
    exact mem_flatDomain_self Φ⟩
  have hWs : W⊆e.source:=fun _ h=>h.1.1
  have heAtlas : e∈atlas (ComplexModel (n+1)) Z := by
    cases R with
    | refl => rw [hA.1];exact hA.2
    | step R C π hπ => exact hA.1
  obtain ⟨Θ,hΘs,hΘ0,hΘ⟩:=exists_inherited_coordinates e heAtlas z hz he0 W hW hzW hWs
  have hVector:=first_vector x c hck hcj Φ hOld R e hA
  have hMask : ∀v∈flatDomain Θ,v∈W ∧ flatMap Θ v=e v ∧
      (v∈(Q0.geoTransformAlong R).N↔flatMap Θ v∈coordSubspace SN) := by
    intro v hv
    have hd:=hΘ v hv
    refine ⟨hd.1,hd.2,?_⟩
    rw [hd.2]
    exact hV.2.1 v hd.1.1
  refine ⟨W,Θ,hκz,rfl,hW,hzW,hWs,hΘs,hΘ0,hMask,?_,?_⟩
  · intro v hv
    exact ⟨hv.2,hVector v hv.1.1⟩
  · have hRS : Tendsto (maskRetract SN) (𝓝 0) (𝓝 0) := by
      simpa only [map_zero] using (maskRetract SN).continuous.tendsto 0
    have hTarget : ∀ᶠw in 𝓝 (0 : ComplexModel (n+1)),maskRetract SN w∈Θ.target :=
      hRS.eventually (Θ.isOpen_target.mem_nhds (zero_mem_target hΘ0))
    filter_upwards [hTarget] with w hw
    have hDom:=flatInv_mem_flatDomain hw hΘs
    have hd:=hMask (flatInv Θ (maskRetract SN w)) hDom
    have heν : e (flatInv Θ (maskRetract SN w))=maskRetract SN w :=
      hd.2.1.symm.trans (flatMap_flatInv hw hΘs)
    have hc:=hVector (flatInv Θ (maskRetract SN w)) hd.1.1.1
    rw [heν,mask_base SN hSN] at hc
    calc
      κ (flatInv Θ (maskRetract SN w))=
          flatInv Φ (flatMap Φ (κ (flatInv Θ (maskRetract SN w)))) :=
        (flatInv_flatMap hd.1.2).symm
      _=flatInv Φ (maskRetract (oldMask SN) (iteratedVerticalBase n (R.length+1) w)) :=
        congrArg (flatInv Φ) hc

private theorem masked_holomorphic {n : ℕ} {X : CMfd.{u} n} {x : X}
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (hΦs : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (S : Finset (Fin n)) (f : X→ℂ) (hf : HolomorphicAt n f x) :
    HolomorphicAt n (maskFlatten Φ S f) 0 := by
  let ν : ComplexModel n→X:=fun w=>flatInv Φ (maskRetract S w)
  have hν0 : ν 0=x := by change flatInv Φ (maskRetract S 0)=x;rw [map_zero,flatInv_zero hΦ0]
  have hRS : Tendsto (maskRetract S) (𝓝 0) (𝓝 0) := by
    simpa only [map_zero] using (maskRetract S).continuous.tendsto 0
  have hT : ∀ᶠw in 𝓝 (0 : ComplexModel n),maskRetract S w∈Φ.target :=
    hRS.eventually (Φ.isOpen_target.mem_nhds (zero_mem_target hΦ0))
  have hν : ∀ᶠw in 𝓝 (0 : ComplexModel n),
      MDifferentiableAt 𝓘(ℂ,ComplexModel n) 𝓘(ℂ,ComplexModel n) ν w := by
    filter_upwards [hT] with w hw
    exact (mdifferentiableAt_flatInv hΦs hw).comp w
      (maskRetract S).differentiableAt.mdifferentiableAt
  exact HadamardBridge.holomorphicAt_comp_map hν (by
    change HolomorphicAt n f (ν 0)
    rw [hν0]
    exact hf)

/- Reducible OUTPUT notation for ALL scalar queries, never an input packet. -/
private abbrev scalarFunctionOutput {n : ℕ} {X : CMfd.{u} n} {Z : CMfd.{u} (n+1)}
    (N : Set X) (Nt : Set Z) (x : X) (z : Z)
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (Θ : LocalHolomorphicEquivAt (n:=n+1) (chartAt (ComplexModel (n+1)) z z))
    (SN : Finset (Fin (n+1))) (r : ℕ) (κ : Z→X) : Prop :=
  ∀(f : X→ℂ) (_hf : HolomorphicAt n f x),
    let F:=maskFlatten Φ (oldMask SN) f
    let G:=maskFlatten Θ SN (f∘κ)
    ∃(hF : ∀ᶠw in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ F w)
      (hG : ∀ᶠw in 𝓝 (0 : ComplexModel (n+1)),DifferentiableAt ℂ G w),
      HolGerm.mk G hG=iteratedVerticalGerm (r+1) (HolGerm.mk F hF) ∧
      (∀t : ℕ,VanishesToOrderOn (n+1) Nt z t (f∘κ) ↔
        ∀α : Fin n→₀ℕ,(r+2)*normalExponentDegree α<t →
          MvPowerSeries.coeff α (actualUnshiftedTaylorAlgHom n (HolGerm.mk F hF))=0) ∧
      (∀a : ℕ,VanishesToOrderOn (n+1) Nt z ((r+2)*a) (f∘κ) ↔
        VanishesToOrderOn n N x a f) ∧
      (∀a b : ℕ,b≤r+1 →
        (VanishesToOrderOn (n+1) Nt z ((r+2)*a+b+1) (f∘κ) ↔
          VanishesToOrderOn n N x (a+1) f)) ∧
      (actualUnshiftedTaylorAlgHom (n+1) (HolGerm.mk G hG)).order=
        ((r+2 : ℕ) : ℕ∞)*(actualUnshiftedTaylorAlgHom n (HolGerm.mk F hF)).order

private theorem scalar_from_geometry {n : ℕ} {X : CMfd.{u} n} {Z : CMfd.{u} (n+1)}
    (N : Set X) (Nt : Set Z) (x : X) (z : Z)
    (Φ : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (hΦs : Φ.source⊆(chartAt (ComplexModel n) x).target)
    (hΦ0 : Φ.toFun (chartAt (ComplexModel n) x x)=0)
    (Θ : LocalHolomorphicEquivAt (n:=n+1) (chartAt (ComplexModel (n+1)) z z))
    (hΘs : Θ.source⊆(chartAt (ComplexModel (n+1)) z).target)
    (hΘ0 : Θ.toFun (chartAt (ComplexModel (n+1)) z z)=0)
    (SN : Finset (Fin (n+1))) (r : ℕ) (κ : Z→X)
    (hκ : ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞ κ)
    (hκz : κ z=x)
    (hSource : ∀v∈flatDomain Φ,v∈N↔flatMap Φ v∈coordSubspace (oldMask SN))
    (hTarget : ∀v∈flatDomain Θ,v∈Nt↔flatMap Θ v∈coordSubspace SN)
    (hPoint : ∀ᶠw in 𝓝 (0 : ComplexModel (n+1)),
      κ (flatInv Θ (maskRetract SN w))=
        flatInv Φ (maskRetract (oldMask SN) (iteratedVerticalBase n (r+1) w))) :
    scalarFunctionOutput N Nt x z Φ Θ SN r κ := by
  intro f hf
  let F:=maskFlatten Φ (oldMask SN) f
  let G:=maskFlatten Θ SN (f∘κ)
  have hfκ : HolomorphicAt (n+1) (f∘κ) z := HadamardBridge.holomorphicAt_comp_map
    (Eventually.of_forall fun v=>hκ.contMDiffAt.mdifferentiableAt (by simp)) (by rw [hκz];exact hf)
  have hFh:=masked_holomorphic Φ hΦs hΦ0 (oldMask SN) f hf
  have hGh:=masked_holomorphic Θ hΘs hΘ0 SN (f∘κ) hfκ
  have hF : ∀ᶠw in 𝓝 (0 : ComplexModel n),DifferentiableAt ℂ F w:=hFh.mono fun _ h=>h.differentiableAt
  have hG : ∀ᶠw in 𝓝 (0 : ComplexModel (n+1)),DifferentiableAt ℂ G w:=hGh.mono fun _ h=>h.differentiableAt
  have hEq : HolGerm.mk G hG=iteratedVerticalGerm (r+1) (HolGerm.mk F hF) := by
    rw [iterated_vertical_germ_mk]
    apply HolGerm.mk_eq_mk_iff.mpr
    filter_upwards [hPoint] with w hw
    exact congrArg f hw
  have hS (a : ℕ) : VanishesToOrderOn n N x a f ↔
      HolGerm.mk F hF∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel n))^a :=
    (vanishesToOrderOn_iff_mask_point_power Φ hΦs hΦ0 (oldMask SN)
      (fun h1 h2=>hSource _ ⟨h1,h2⟩) f hf a).trans
      (mem_maximalIdeal_pow_iff_point_power hF a).symm
  have hT (a : ℕ) : VanishesToOrderOn (n+1) Nt z a (f∘κ) ↔
      HolGerm.mk G hG∈IsLocalRing.maximalIdeal (HolGerm (ComplexModel (n+1)))^a :=
    (vanishesToOrderOn_iff_mask_point_power Θ hΘs hΘ0 SN
      (fun h1 h2=>hTarget _ ⟨h1,h2⟩) (f∘κ) hfκ a).trans
      (mem_maximalIdeal_pow_iff_point_power hG a).symm
  refine ⟨hF,hG,hEq,?_,?_,?_,?_⟩
  · intro t
    exact (hT t).trans (by rw [hEq];exact iterated_vertical_maximal_cut n (r+1) t (HolGerm.mk F hF))
  · intro a
    exact ((hT ((r+2)*a)).trans (by
      rw [hEq];exact iterated_vertical_maximal_multiple_cut n (r+1) a (HolGerm.mk F hF))).trans (hS a).symm
  · intro a b hb
    exact ((hT ((r+2)*a+b+1)).trans (by
      rw [hEq];exact iterated_vertical_maximal_successor_cut n (r+1) a b hb (HolGerm.mk F hF))).trans (hS (a+1)).symm
  · rw [hEq,iterated_vertical_Taylor]
    exact iterated_vertical_order n (r+1) (actualUnshiftedTaylorAlgHom n (HolGerm.mk F hF))

private instance point_closed_fact {r : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (ComplexModel r) X] [IsComplexManifold r X] (x : X) :
    Fact (IsClosedSubmanifold r ({x} : Set X)) :=
  ⟨(PointSupportedIdealPrincipalization.singleton_geometry_and_coherence x).1⟩

private abbrev recordMark {r : ℕ} (X : CMfd.{u} r) (Q : MarkedIdeal r X) : ℕ :=
  @MarkedIdeal.d r X.carrier X.topologicalSpace X.chartedSpace Q
private abbrev recordBoundary {r : ℕ} (X : CMfd.{u} r) (Q : MarkedIdeal r X) : List (Set X) :=
  @MarkedIdeal.E r X.carrier X.topologicalSpace X.chartedSpace Q

/- Entire first native seed is retained; all added records are OUTPUT notation. -/
private abbrev originalScalarOutput {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp)
    (Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
    (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
    (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
    (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))) : Prop :=
  let p : projectionAmbient X := (x,0)
  let C : Set (projectionAmbient X) := {p}
  let _ : Fact (IsClosedSubmanifold (n+1) C) := ⟨(projection_point_centre M hM x hx).1.1⟩
  let Y : CMfd.{u} (n+1) := CMfd.of (BlowupSpace (n+1) C)
  let π : Y→projectionAmbient X := blowupProj (n+1) C
  let Q : MarkedIdeal (n+1) Y := (projectionTest M).geoTransform C π
  let z := c.invFun 0
  Φ.source⊆(chartAt (ComplexModel n) x).target ∧ Φ.toFun (chartAt (ComplexModel n) x x)=0 ∧
  c.y₀=p ∧ c.k=0 ∧ c.j=Fin.last n ∧
  (∀(y : projectionAmbient X)(i : Fin n),flatCoord c.Φ (i.castAdd 1) y=flatCoord Φ i y.1) ∧
  (∀y : projectionAmbient X,flatCoord c.Φ (Fin.last n) y=y.2 0) ∧
  (∀y∈flatDomain c.Φ,y∈(projectionTest M).N ↔
    c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀ y)∈coordSubspace SN) ∧
  (∀i,x∈M.E.get i→∀y∈flatDomain c.Φ,y∈(Prod.fst : projectionAmbient X→X) ⁻¹' M.E.get i ↔
    c.Φ.toFun (chartAt (ComplexModel (n+1)) c.y₀ y)∈coordSubspace (SE i)) ∧
  Fin.last n∉SN ∧ (∀i,Fin.last n∉SE i) ∧ (0 : ComplexModel (n+1))∈c.target ∧
  z∈c.source ∧ π z=p ∧ c.toFun z=0 ∧ IsBlowupAlong (n+1) C π ∧
  c.homeo∈atlas (ComplexModel (n+1)) Y ∧ IsInvDomain (k+1) Q ∧ z∈Q.cosupp ∧
  recordMark Y Q=M.d ∧
  recordBoundary Y Q=M.E.map (fun H=>geoStrictTransform π C ((Prod.fst : projectionAmbient X→X) ⁻¹' H))++
    [geoStrictTransform π C (horizontal X),π ⁻¹' C] ∧
  (recordBoundary Y Q).length=M.E.length+2 ∧
  IsOpen U ∧ z∈U ∧ U⊆c.source ∧
  (∀v∈U,v∈Q.N↔c.toFun v∈coordSubspace SN) ∧
  (∀i,(x∈M.E.get i→∀v∈U,v∈geoStrictTransform π C ((Prod.fst : projectionAmbient X→X) ⁻¹' M.E.get i)↔
      c.toFun v∈coordSubspace (SE i)) ∧
    (x∉M.E.get i→∀v∈U,v∉geoStrictTransform π C ((Prod.fst : projectionAmbient X→X) ⁻¹' M.E.get i))) ∧
  (∀v∈U,v∉geoStrictTransform π C (horizontal X)) ∧
  (∀v∈U,v∈π ⁻¹' C↔c.toFun v (Fin.last n)=0) ∧

  Φs.toFun=Φ.toFun ∧ Φs.invFun=Φ.invFun ∧
  Φs.source⊆Φ.source ∧ Φs.target⊆Φ.target ∧
  Φs.source⊆(chartAt (ComplexModel n) x).target ∧
  Φs.toFun (chartAt (ComplexModel n) x x)=0 ∧
  flatDomain Φs=flatDomain Φ∩(fun y : X=>((y,0) : projectionAmbient X)) ⁻¹' flatDomain c.Φ ∧
  (∀y∈flatDomain Φs,y∈M.N↔flatMap Φs y∈coordSubspace (oldMask SN)) ∧
  ∀{Z : CMfd.{u} (n+1)} (R : BlowupTower Y Z)
    (e : OpenPartialHomeomorph Z (ComplexModel (n+1)))
    (_hA : AnchoredInheritedLastChartChain c.homeo R e)
    (w : Z) (_hw : w∈e.source) (_hew : e w=0),
    let κ : Z→X:=(Prod.fst : projectionAmbient X→X)∘π∘R.proj
    ∃(W : Set Z)
      (Θ : LocalHolomorphicEquivAt (n:=n+1) (chartAt (ComplexModel (n+1)) w w)),
      κ w=x ∧ W=e.source∩R.proj ⁻¹' (U∩c.source)∩κ ⁻¹' flatDomain Φs ∧
      IsOpen W ∧ w∈W ∧ W⊆e.source ∧
      Θ.source⊆(chartAt (ComplexModel (n+1)) w).target ∧
      Θ.toFun (chartAt (ComplexModel (n+1)) w w)=0 ∧
      (∀v∈flatDomain Θ,v∈W ∧ flatMap Θ v=e v ∧
        (v∈(Q.geoTransformAlong R).N↔flatMap Θ v∈coordSubspace SN)) ∧
      (∀v∈W,κ v∈flatDomain Φs ∧
        flatMap Φs (κ v)=iteratedVerticalBase n (R.length+1) (e v)) ∧
      (∀ᶠt in 𝓝 (0 : ComplexModel (n+1)),
        κ (flatInv Θ (maskRetract SN t))=
          flatInv Φs (maskRetract (oldMask SN) (iteratedVerticalBase n (R.length+1) t))) ∧
      scalarFunctionOutput M.N (Q.geoTransformAlong R).N x w Φ Θ SN R.length κ

/-- ONLY ordinary original inputs choose ONE actual original/native first seed
before ALL tails/points/functions. Every source, inverse, germ and cut guard is derived. -/
theorem exists_original_anchored_scalar_cuts {n k : ℕ} {X : CMfd.{u} n}
    (M : MarkedIdeal n X) (hM : IsInvDomain k M) (x : X) (hx : x∈M.cosupp) :
    ∃(Φ Φs : LocalHolomorphicEquivAt (n:=n) (chartAt (ComplexModel n) x x))
      (c : FlatChart (n+1) ({(x,0)} : Set (projectionAmbient X)))
      (SN : Finset (Fin (n+1))) (SE : Fin M.E.length→Finset (Fin (n+1)))
      (U : Set (BlowupSpace (n+1) ({(x,0)} : Set (projectionAmbient X)))),
      originalScalarOutput M hM x hx Φ Φs c SN SE U := by
  obtain ⟨Φ,c,SN,SE,U,hSeed⟩:=exists_original_anchored_current_carrier_mask M hM x hx
  rcases hSeed with ⟨hΦs,hΦ0,hcp,hck,hcj,hOld,hLast,hSourceN,hSourceE,hSN,hSE,h0c,
    hzSource,hzp,hWz,hπ,hAtlas,hQ,hzQ,hdQ,hEword,hLength,hU,hzU,hUc,hNmask,
    hEmask,hEmptyH,hBorn,_hAnchor0,_hTails⟩
  obtain ⟨Φs,hTo,hInv,hSub,hTSub,hSrc,hZero,hDom,hSource⟩:=
    source_mask_restriction M.N x Φ hΦs hΦ0 c hcp SN hOld hLast hSourceN
  refine ⟨Φ,Φs,c,SN,SE,U,?_⟩
  dsimp only [originalScalarOutput]
  refine ⟨hΦs,hΦ0,hcp,hck,hcj,hOld,hLast,hSourceN,hSourceE,hSN,hSE,h0c,
    hzSource,hzp,hWz,hπ,hAtlas,hQ,hzQ,hdQ,hEword,hLength,hU,hzU,hUc,hNmask,
    hEmask,hEmptyH,hBorn,hTo,hInv,hSub,hTSub,hSrc,hZero,hDom,hSource,?_⟩
  intro Z R e hA w hw hew
  let C : Set (projectionAmbient X):={(x,0)}
  let Y : CMfd.{u} (n+1):=CMfd.of (BlowupSpace (n+1) C)
  let π : Y→projectionAmbient X:=blowupProj (n+1) C
  let Q : MarkedIdeal (n+1) Y:=(projectionTest M).geoTransform C π
  let κ : Z→X:=(Prod.fst : projectionAmbient X→X)∘π∘R.proj
  have hOlds (y : projectionAmbient X) (i : Fin n) :
      flatCoord c.Φ (i.castAdd 1) y=flatCoord Φs i y.1 := by
    simpa only [flatCoord,hTo] using hOld y i
  obtain ⟨W,Θ,hκw,hW,hWo,hwW,hWs,hΘs,hΘ0,hMask,hVector,hPoint⟩:=
    anchored_original_inverse_square x c hck hcj Φs hSrc hZero hOlds h0c hzp
      Q SN hSN U hU hzU hUc hNmask R e hA w hw hew
  refine ⟨W,Θ,hκw,hW,hWo,hwW,hWs,hΘs,hΘ0,hMask,hVector,hPoint,?_⟩
  have hκ : ContMDiff 𝓘(ℂ,ComplexModel (n+1)) 𝓘(ℂ,ComplexModel n) ∞ κ :=
    ((ProductComplexManifold.contMDiff_fst (n:=n) (m:=1) (X:=X) (Y:=ComplexModel 1)).comp
      contMDiff_blowupProj).comp R.contMDiff_proj
  have hs:=scalar_from_geometry M.N (Q.geoTransformAlong R).N x w Φs hSrc hZero
    Θ hΘs hΘ0 SN R.length κ hκ hκw hSource (fun v hv=>(hMask v hv).2.2) hPoint
  intro f hf
  have hFlat : maskFlatten Φs (oldMask SN) f=maskFlatten Φ (oldMask SN) f := by
    funext t
    change f ((chartAt (ComplexModel n) x).symm (Φs.invFun (maskRetract (oldMask SN) t)))=
      f ((chartAt (ComplexModel n) x).symm (Φ.invFun (maskRetract (oldMask SN) t)))
    rw [hInv]
  have hfOut:=hs f hf
  simpa only [hFlat] using hfOut

end
end Hironaka.HironakaActualAnchoredOriginalGermSquare
