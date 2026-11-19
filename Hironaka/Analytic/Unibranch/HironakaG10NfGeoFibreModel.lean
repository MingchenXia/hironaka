import Hironaka.Analytic.Unibranch.HironakaG10NfFibreModelOrigin
import Hironaka.Analytic.Unibranch.HironakaG10NfFlatTransport
import Hironaka.Analytic.Unibranch.HironakaG10GlStepSquare

/-!
# H3.4 (transport): local fibre-product models over the GEOMETRIC blowup give `FibreModel₀` over the native step

Lane G10H3, run 0081.  The canonical charts describe the geometric blowup `Bl_B X`
(`OriginalFiniteIdealGeometricBlowup.sourceObject`) with its projection `πT`, the strict transform `Y'` with its
projection `q` and the induced map `ind : Y' ⟶ Bl_B X`; one step of the flattening algorithm uses the native blowup,
isomorphic to `Bl_B X` over the base (`HironakaG10SbBlowupComparison.blowupIso`, BC3), with `f' = ind ≫ blowupIso.inv`
(`HironakaG10GlStepSquare.stepP_eq_inducedMorphism_blowupIso_inv`).

* `GeoFibreModel` — the fields of `HironakaG10NfFibreModelOrigin.FibreModel₀` read over `Bl_B X` (for a family `H` of
  ideals of `Bl_B X`, standing for the transported local flattener `Z₁`), with the centre generator condition for
  EVERY regular generator;
* **`fibreModel₀_of_geo`** — transport along `blowupIso`: a geometric model at `(y, blowupIso x')` for the transported
  `Z₁` is a `FibreModel₀ s c Z₁ y x'`.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory AlgebraicGeometry Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10NfGeoFibreModel

open Hironaka HironakaG10ChowFibreAlgebra HironakaSingularModuleSheafStalk
  HironakaG10HirFlatQuotient HironakaG10ChowArtinReesCentre HironakaNativePulledIdealSheaf
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform Hironaka.Analytic.Unibranch.HironakaG10ChowFibreChain
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus
  Hironaka.Analytic.Unibranch.HironakaG10GlLeavingContradiction Hironaka.Analytic.Unibranch.HironakaG10SbTorsionSaturation
  Hironaka.Analytic.Unibranch.HironakaG10SbBlowupComparison Hironaka.Analytic.Unibranch.HironakaG10NfFibreModelOrigin
  Hironaka.Analytic.Unibranch.HironakaG10NfFlatTransport

noncomputable section

variable {X Y : SourceReducedComplexSpace}
  (B : SheafOfModules.{0} (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  (b : B ⟶ SheafOfModules.unit (forgetRing Y.obj.left.toSheafedSpace.sheaf))
  [B.IsFiniteType] (F : X ⟶ Y)

local instance : (nativePulledIdealModule F.hom.left B b).IsFiniteType :=
  HironakaNativePulledIdealFiniteType.nativePulledIdealModule_isFiniteType F.hom.left B b

/-- The stalk ideal of the centre `b·𝒪_Y`. -/
abbrev geoCentre (P : Y.obj.left) : Ideal (Y.obj.left.presheaf.stalk P) :=
  (LinearMap.range (stalkInclusionLinearMap Y.obj.left.toSheafedSpace.sheaf B b P) :)

/-- **A local model of `X ×_Y Bl_B Y` near `(x, Q₀)` over the geometric blowup.** -/
structure GeoFibreModel
    (H : ∀ Q : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left,
      Ideal ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.stalk Q))
    (x : X.obj.left) (Q₀ : (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left) where
  W : Type
  [top : TopologicalSpace W]
  w₀ : W
  pY : W → X.obj.left
  pT : W → (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left
  pY_w₀ : pY w₀ = x
  pT_w₀ : pT w₀ = Q₀
  square : ∀ w, F.hom.left.base (pY w) =
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base (pT w)
  cover : ∀ U ∈ 𝓝 w₀, ∀ᶠ p in 𝓝 (x, Q₀),
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base p.2 ∈ nonunitLocus B b →
    F.hom.left.base p.1 = (OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base p.2 →
      ∃ w ∈ U, pY w = p.1 ∧ pT w = p.2
  Bw : W → Type
  [ring : ∀ w, CommRing (Bw w)]
  [noetherian : ∀ w, IsNoetherianRing (Bw w)]
  ψ : ∀ w, (OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.stalk (pT w) →+* Bw w
  T : ∀ w, Ideal (Bw w)
  local₀ : Ideal.map (ψ w₀) (IsLocalRing.maximalIdeal _) ≤ Ideal.jacobson ⊥
  T_w₀ : ∀ g, IsRegular g →
    Ideal.map ((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.stalkMap (pT w₀)).hom
      (geoCentre B b ((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base (pT w₀))) =
        Ideal.span {g} → T w₀ = powerSat (⊥ : Ideal (Bw w₀)) (ψ w₀ g)
  flat_base₀ : ∀ J : Ideal (Y.obj.left.presheaf.stalk
      ((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.base (pT w₀))),
    (quotMap (fibreStalkMap F _ (pY w₀) (square w₀)) J).Flat →
      (quotMap (ψ w₀) (Ideal.map
        ((OriginalFiniteIdealGeometricBlowup.projectionMorphism B b).hom.left.stalkMap (pT w₀)).hom J)).Flat
  strict : ∀ w, T w ≤ Ideal.map (ψ w) (IsLocalRing.maximalIdeal _) →
    ∃ y'' : (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).obj.left,
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).hom.left.base y'' = pY w ∧
      (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base y'' = pT w ∧
      Ideal.comap ((OriginalFiniteIdealGeometricBlowup.projectionMorphism (nativePulledIdealModule F.hom.left B b)
          (nativePulledIdealInclusion F.hom.left B b)).hom.left.stalkMap y'').hom
          (fibreIdealAt (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F) y'') ≤
        fibreIdealAt F ((OriginalFiniteIdealGeometricBlowup.projectionMorphism
          (nativePulledIdealModule F.hom.left B b) (nativePulledIdealInclusion F.hom.left B b)).hom.left.base y'')
  strict₀ : T w₀ ≤ Ideal.map (ψ w₀) (IsLocalRing.maximalIdeal _) →
    ∃ (y'' : (OriginalFiniteIdealGeometricBlowup.sourceObject (nativePulledIdealModule F.hom.left B b)
        (nativePulledIdealInclusion F.hom.left B b)).obj.left)
      (hp : (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F).hom.left.base y'' = pT w₀),
      ∀ J₁ : Ideal ((OriginalFiniteIdealGeometricBlowup.sourceObject B b).obj.left.presheaf.stalk (pT w₀)),
        (quotMap (fibreStalkMap (OriginalFiniteIdealBlowupSquare.inducedMorphism B b F) (pT w₀) y'' hp) J₁).Flat →
          (quotMap ((Ideal.Quotient.mk (T w₀)).comp (ψ w₀)) J₁).Flat
  spread : T w₀ ≤ Ideal.map (ψ w₀) (H (pT w₀)) → ∀ᶠ w in 𝓝 w₀, T w ≤ Ideal.map (ψ w) (H (pT w))

attribute [instance] GeoFibreModel.top GeoFibreModel.ring GeoFibreModel.noetherian

/-! ### Generic transports -/

/-- A ring isomorphism preserves regular elements. -/
theorem isRegular_equiv {A A' : Type*} [CommRing A] [CommRing A'] (e : A ≃+* A') {a : A} (h : IsRegular a) :
    IsRegular (e a) := by
  refine (Commute.isRegular_iff (fun z => Commute.all _ z)).mpr ?_
  intro u v huv
  have h1 : a * e.symm u = a * e.symm v := by
    apply e.injective
    simpa only [map_mul, RingEquiv.apply_symm_apply] using huv
  have h2 := h.1 h1
  simpa only [RingEquiv.apply_symm_apply] using congrArg e h2

/-- Base-point transport of the fibre flatness of a morphism. -/
theorem flat_fibreStalkMap_transport {X₀ Y₀ : SourceReducedComplexSpace} (f : X₀ ⟶ Y₀) (x₀ : X₀.obj.left)
    {P₁ P₂ : Y₀.obj.left} (h : P₁ = P₂) (h₁ : f.hom.left.base x₀ = P₁) (h₂ : f.hom.left.base x₀ = P₂)
    (J : Ideal (Y₀.obj.left.presheaf.stalk P₁)) (hJ : (quotMap (fibreStalkMap f P₁ x₀ h₁) J).Flat) :
    (quotMap (fibreStalkMap f P₂ x₀ h₂) (J.map (eqToHom (congrArg Y₀.obj.left.presheaf.stalk h)).hom)).Flat := by
  subst h
  rw [eqToHom_refl, CommRingCat.hom_id, Ideal.map_id]
  exact hJ

omit [B.IsFiniteType] in
/-- Base-point transport of a stalk ideal of the centre. -/
theorem geoCentre_transport {P₁ P₂ : Y.obj.left} (h : P₁ = P₂) :
    (geoCentre B b P₁).map (eqToHom (congrArg Y.obj.left.presheaf.stalk h)).hom = geoCentre B b P₂ := by
  subst h
  simp

/-! ### The native step and the geometric blowup -/

section Step

attribute [local instance] AdmissibleCentre.finiteType

variable (s : Stage) (c : AdmissibleCentre s.f)

/-- The inverse comparison `Bl_B X ⟶ X'` of locally ringed spaces. -/
abbrev invMap : (OriginalFiniteIdealGeometricBlowup.sourceObject c.B c.b).obj.left ⟶ (nextWith s c).X.obj.left :=
  (blowupIso c.B c.b c.dense).inv.hom.left

instance invMap_isIso : IsIso (invMap s c) :=
  ⟨⟨(blowupIso c.B c.b c.dense).hom.hom.left,
    congrArg (fun f => f.hom.left) (blowupIso c.B c.b c.dense).inv_hom_id,
    congrArg (fun f => f.hom.left) (blowupIso c.B c.b c.dense).hom_inv_id⟩⟩

instance invMap_isOpenImmersion : LocallyRingedSpace.IsOpenImmersion (invMap s c) := inferInstance

/-- The stalk isomorphism of the comparison. -/
noncomputable def invEquiv (Q : (OriginalFiniteIdealGeometricBlowup.sourceObject c.B c.b).obj.left) :
    (nextWith s c).X.obj.left.presheaf.stalk ((invMap s c).base Q) ≃+*
      (OriginalFiniteIdealGeometricBlowup.sourceObject c.B c.b).obj.left.presheaf.stalk Q :=
  Hironaka.Analytic.Unibranch.HironakaG10NfStalkSquare.oiStalkEquiv (invMap s c) Q

theorem invEquiv_toRingHom (Q : (OriginalFiniteIdealGeometricBlowup.sourceObject c.B c.b).obj.left) :
    (invEquiv s c Q).toRingHom = ((invMap s c).stalkMap Q).hom :=
  RingHom.ext fun r => Hironaka.Analytic.Unibranch.HironakaG10NfStalkSquare.oiStalkEquiv_apply (invMap s c) Q r

/-- The transported local flattener family on `Bl_B X`. -/
def transH (Z₁ : LocalFlattener (nextWith s c).f)
    (Q : (OriginalFiniteIdealGeometricBlowup.sourceObject c.B c.b).obj.left) :
    Ideal ((OriginalFiniteIdealGeometricBlowup.sourceObject c.B c.b).obj.left.presheaf.stalk Q) :=
  Ideal.map ((invMap s c).stalkMap Q).hom (Z₁.H ((invMap s c).base Q))

theorem sigma_inv_base (Q : (OriginalFiniteIdealGeometricBlowup.sourceObject c.B c.b).obj.left) :
    (stepσ s c).hom.left.base ((invMap s c).base Q) =
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism c.B c.b).hom.left.base Q :=
  congrArg (fun k => k.hom.left.base Q) (blowupIso_inv_comp c.B c.b c.dense)

theorem inv_hom_base (x' : (nextWith s c).X.obj.left) :
    (invMap s c).base ((blowupIso c.B c.b c.dense).hom.hom.left.base x') = x' :=
  congrArg (fun k => k.hom.left.base x') (blowupIso c.B c.b c.dense).hom_inv_id

theorem piT_hom_base (x' : (nextWith s c).X.obj.left) :
    (OriginalFiniteIdealGeometricBlowup.projectionMorphism c.B c.b).hom.left.base
        ((blowupIso c.B c.b c.dense).hom.hom.left.base x') = (stepσ s c).hom.left.base x' :=
  congrArg (fun k => k.hom.left.base x') (blowupIso_hom_comp c.B c.b c.dense)

theorem inv_sigma_stalk (Q : (OriginalFiniteIdealGeometricBlowup.sourceObject c.B c.b).obj.left)
    (a : s.X.obj.left.presheaf.stalk ((stepσ s c).hom.left.base ((invMap s c).base Q))) :
    ((invMap s c).stalkMap Q).hom (((stepσ s c).hom.left.stalkMap ((invMap s c).base Q)).hom a) =
      ((OriginalFiniteIdealGeometricBlowup.projectionMorphism c.B c.b).hom.left.stalkMap Q).hom
        ((eqToHom (congrArg s.X.obj.left.presheaf.stalk (sigma_inv_base s c Q))).hom a) := by
  have H : invMap s c ≫ (stepσ s c).hom.left =
      (OriginalFiniteIdealGeometricBlowup.projectionMorphism c.B c.b).hom.left :=
    congrArg (fun k => k.hom.left) (blowupIso_inv_comp c.B c.b c.dense)
  have e := stalkMap_eq_of_eq _ _ H Q (sigma_inv_base s c Q).symm a
  have c1 := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp (invMap s c) (stepσ s c).hom.left Q) a
  exact c1.symm.trans e

/-- The fibre ideal of the native strict-transform map is that of the induced map. -/
theorem fibreIdealAt_step (y'' : (nextWith s c).Y.obj.left) :
    fibreIdealAt (nextWith s c).f y'' = fibreIdealAt (OriginalFiniteIdealBlowupSquare.inducedMorphism c.B c.b s.f) y'' := by
  have h : (nextWith s c).f.hom.left =
      (OriginalFiniteIdealBlowupSquare.inducedMorphism c.B c.b s.f).hom.left ≫ invMap s c :=
    congrArg (fun k => k.hom.left) (HironakaG10GlStepSquare.stepP_eq_inducedMorphism_blowupIso_inv s c)
  change lrsFibreIdeal (nextWith s c).f.hom.left y'' = lrsFibreIdeal _ y''
  rw [h, lrsFibreIdeal_comp]
  congr 1
  change Ideal.map _ (IsLocalRing.maximalIdeal _) = IsLocalRing.maximalIdeal _
  rw [← invEquiv_toRingHom]
  exact IsLocalRing.map_maximalIdeal_of_surjective _ (invEquiv s c _).surjective


/-- The fibre stalk map of a composite with an isomorphism. -/
theorem fibreStalkMap_comp {A B' C' : SourceReducedComplexSpace} (f₁ : A ⟶ B') (f₂ : B' ⟶ C') (f : A ⟶ C')
    (H : f = f₁ ≫ f₂) (a : A.obj.left) (Q : B'.obj.left) (hp : f₁.hom.left.base a = Q)
    (hp' : f.hom.left.base a = f₂.hom.left.base Q) :
    fibreStalkMap f (f₂.hom.left.base Q) a hp' = (fibreStalkMap f₁ Q a hp).comp (f₂.hom.left.stalkMap Q).hom := by
  subst H
  subst hp
  ext r
  have c1 := ConcreteCategory.congr_hom (LocallyRingedSpace.stalkMap_comp f₁.hom.left f₂.hom.left a) r
  simp only [fibreStalkMap, eqToHom_refl, CommRingCat.hom_id, RingHom.comp_id, RingHom.comp_apply,
]
  exact c1

/-- **Transport along BC3**: a local model of the fibre product over the geometric blowup at `(y, blowupIso x')`,
for the transported local flattener, is a `FibreModel₀` of the native step at `(y, x')`. -/
theorem fibreModel₀_of_geo (Z₁ : LocalFlattener (nextWith s c).f) (y : s.Y.obj.left)
    (x' : (nextWith s c).X.obj.left)
    (M : GeoFibreModel c.B c.b s.f (transH s c Z₁) y ((blowupIso c.B c.b c.dense).hom.hom.left.base x')) :
    Nonempty (FibreModel₀ s c Z₁ y x') := by
  obtain ⟨g₀, hg₀, hspan⟩ := HironakaG10GlStrictFlatAssembly.exists_regular_centre_generator s c
    ((invMap s c).base (M.pT M.w₀))
  -- the maximal ideal of `X'` maps onto that of `Bl_B X`
  have hmax : ∀ Q, Ideal.map ((invMap s c).stalkMap Q).hom (IsLocalRing.maximalIdeal _) =
      IsLocalRing.maximalIdeal _ := fun Q => by
    rw [← invEquiv_toRingHom]
    exact IsLocalRing.map_maximalIdeal_of_surjective _ (invEquiv s c Q).surjective
  have hT : ∀ w, Ideal.map ((M.ψ w).comp ((invMap s c).stalkMap (M.pT w)).hom) (IsLocalRing.maximalIdeal _) =
      Ideal.map (M.ψ w) (IsLocalRing.maximalIdeal _) := fun w => by
    rw [← Ideal.map_map, hmax]
  have hpf : ∀ y'' : (nextWith s c).Y.obj.left, (nextWith s c).f.hom.left.base y'' =
      (invMap s c).base ((OriginalFiniteIdealBlowupSquare.inducedMorphism c.B c.b s.f).hom.left.base y'') :=
    fun y'' => congrArg (fun k => k.hom.left.base y'')
      (HironakaG10GlStepSquare.stepP_eq_inducedMorphism_blowupIso_inv s c)
  refine ⟨{
    W := M.W
    w₀ := M.w₀
    pY := M.pY
    pX := fun w => (invMap s c).base (M.pT w)
    pY_w₀ := M.pY_w₀
    pX_w₀ := by rw [M.pT_w₀]; exact inv_hom_base s c x'
    square := fun w => (M.square w).trans (sigma_inv_base s c (M.pT w)).symm
    cover := ?_
    B := M.Bw
    ψ := fun w => (M.ψ w).comp ((invMap s c).stalkMap (M.pT w)).hom
    T := M.T
    local₀ := by rw [hT]; exact M.local₀
    g₀ := g₀
    g₀_regular := hg₀
    span_g₀ := hspan
    T_w₀ := ?_
    flat_base₀ := ?_
    strict := ?_
    strict₀ := ?_
    spread := ?_ }⟩
  · -- cover
    intro U hU
    have hc := M.cover U hU
    have hφ : Filter.Tendsto
        (fun p : s.Y.obj.left × (nextWith s c).X.obj.left =>
          (p.1, (blowupIso c.B c.b c.dense).hom.hom.left.base p.2))
        (𝓝 (y, x')) (𝓝 (y, (blowupIso c.B c.b c.dense).hom.hom.left.base x')) :=
      (continuous_fst.prodMk ((blowupIso c.B c.b c.dense).hom.hom.left.base.hom.continuous.comp
        continuous_snd)).tendsto _
    filter_upwards [hφ.eventually hc] with p hp hpc hpf'
    have h1 := piT_hom_base s c p.2
    obtain ⟨w, hw, hw1, hw2⟩ := hp (by rw [h1]; exact hpc) (by rw [h1]; exact hpf')
    refine ⟨w, hw, hw1, ?_⟩
    change (invMap s c).base (M.pT w) = p.2
    rw [hw2]
    exact inv_hom_base s c p.2
  · -- the centre generator
    have hreg : IsRegular (invEquiv s c (M.pT M.w₀) g₀) := isRegular_equiv _ hg₀
    refine M.T_w₀ _ hreg ?_
    have hsp := congrArg (Ideal.map ((invMap s c).stalkMap (M.pT M.w₀)).hom) hspan
    rw [Ideal.map_span, Set.image_singleton, Ideal.map_map] at hsp
    rw [← geoCentre_transport c.B c.b (sigma_inv_base s c (M.pT M.w₀)), Ideal.map_map, ← hsp]
    congr 1
    exact RingHom.ext fun a => (inv_sigma_stalk s c (M.pT M.w₀) a).symm
  · -- base change of flatness
    intro J hJ
    have h12 := sigma_inv_base s c (M.pT M.w₀)
    have hJ' := flat_fibreStalkMap_transport s.f (M.pY M.w₀) h12
      ((M.square M.w₀).trans h12.symm) (M.square M.w₀) J hJ
    have hB := M.flat_base₀ _ hJ'
    have hmap : (Ideal.map ((stepσ s c).hom.left.stalkMap ((invMap s c).base (M.pT M.w₀))).hom J).map
        (invEquiv s c (M.pT M.w₀)).toRingHom =
        (J.map (eqToHom (congrArg s.X.obj.left.presheaf.stalk h12)).hom).map
          ((OriginalFiniteIdealGeometricBlowup.projectionMorphism c.B c.b).hom.left.stalkMap (M.pT M.w₀)).hom := by
      rw [Ideal.map_map, Ideal.map_map, invEquiv_toRingHom]
      congr 1
      exact RingHom.ext fun a => inv_sigma_stalk s c (M.pT M.w₀) a
    rw [← hmap] at hB
    have := flat_quotMap_comp_equiv (invEquiv s c (M.pT M.w₀)) (M.ψ M.w₀) _ hB
    rwa [invEquiv_toRingHom] at this
  · -- the strict transform at nearby pairs
    intro w hw
    obtain ⟨y'', hq, hind, hfib⟩ := M.strict w (by rw [← hT]; exact hw)
    refine ⟨y'', hq, (hpf y'').trans (congrArg (invMap s c).base hind), ?_⟩
    rw [fibreIdealAt_step]
    exact hfib
  · -- the flatness transfer at the origin
    intro hw
    obtain ⟨y'', hp, htr⟩ := M.strict₀ (by rw [← hT]; exact hw)
    refine ⟨y'', (hpf y'').trans (congrArg (invMap s c).base hp), fun J₁ hfl => ?_⟩
    have hfac := fibreStalkMap_comp (OriginalFiniteIdealBlowupSquare.inducedMorphism c.B c.b s.f)
      (blowupIso c.B c.b c.dense).inv (nextWith s c).f
      (HironakaG10GlStepSquare.stepP_eq_inducedMorphism_blowupIso_inv s c) y'' (M.pT M.w₀) hp
      ((hpf y'').trans (congrArg (invMap s c).base hp))
    rw [hfac, ← invEquiv_toRingHom] at hfl
    have h1 := htr _ (flat_quotMap_of_comp_equiv _ _ _ hfl)
    have h2 := flat_quotMap_comp_equiv (invEquiv s c (M.pT M.w₀))
      ((Ideal.Quotient.mk (M.T M.w₀)).comp (M.ψ M.w₀)) J₁ h1
    rw [invEquiv_toRingHom] at h2
    exact h2
  · -- spread
    intro _ h
    have hH : ∀ w, Ideal.map ((M.ψ w).comp ((invMap s c).stalkMap (M.pT w)).hom)
        (Z₁.H ((invMap s c).base (M.pT w))) = Ideal.map (M.ψ w) (transH s c Z₁ (M.pT w)) :=
      fun w => (Ideal.map_map _ _).symm
    rw [hH] at h
    filter_upwards [M.spread h] with w hw
    rw [hH]
    exact hw

end Step

end

end Hironaka.Analytic.Unibranch.HironakaG10NfGeoFibreModel
