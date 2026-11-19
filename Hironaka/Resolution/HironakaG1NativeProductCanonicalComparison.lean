import Hironaka.Resolution.HironakaG1NativeFiniteProductState
import Hironaka.Resolution.HironakaG1OriginalUnequalMarkCanonical
import Hironaka.Resolution.HironakaG1OriginalInvariantClassFunctorial
import Hironaka.Resolution.HironakaSmoothSubmersionOriginalAmbientCanonical
import Hironaka.Resolution.HironakaSmoothSubmersionComposition
import Hironaka.Resolution.HironakaSmoothSubmersionOrderedGlobalTrace

/-! Ordinary independent native records on a TRUE smooth product window.
Full mathematical Blueprint FIRST:
hironaka-g1-native-product-canonical-comparison.tex.
Only actual COMMON WHOLE powers have equal full values. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set Filter Classical TopologicalSpace
open scoped Topology Manifold ContDiff
namespace Hironaka.HironakaG1NativeProductCanonicalComparison
noncomputable section
open Hironaka.HolomorphicIdealSheaves Hironaka.BlowupSequences
  MarkedIdeals MarkedIdeals.MarkedIdeal MarkedIdealBiholomorphism
  BlowupTowers BlowupTowerTransforms ResolutionInvariantSpec CanonicalCentres
  HironakaG11PresLineState HironakaG11PresLineStable HironakaG1NativeFiniteProductState
  HironakaG8LocalHistory HironakaG8LocalPower HironakaG11InvBMClass
  HironakaActualPowerBoundaryExponents HironakaG1OriginalUnequalMarkCanonical
  HironakaG1OriginalInvariantClassFunctorial ResolutionDriver
  HironakaSmoothSubmersionCoefficientIdeals HironakaSmoothSubmersionRelativeGeometry
  HironakaSmoothSubmersionCartesianTower HironakaSmoothSubmersionRelativeControlledTower
  HironakaSmoothSubmersionOriginalAmbientCanonical HironakaSmoothSubmersionComposition
  HironakaSmoothSubmersionOrderedGlobalTrace HironakaSmoothSubmersionOrderedChoiceImageTrace

open scoped ProductComplexManifold

variable {n r : ℕ} {X : CMfd.{0} n}

def windowProjection (X : CMfd.{0} n) (r : ℕ)
    (O : Opens (finiteProductAmbient X r)) : O → X := Prod.fst ∘ Subtype.val

def windowRecord (Q : MarkedIdeal n X) (r : ℕ)
    (O : Opens (finiteProductAmbient X r)) : MarkedIdeal (n+r) (CMfd.of (n := n+r) O) :=
  markedPullback (windowProjection X r O) Q

theorem window_isSubmersion (X : CMfd.{0} n) (r : ℕ)
    (O : Opens (finiteProductAmbient X r)) :
    Manifold.IsSubmersion 𝓘(ℂ,ComplexModel (n+r)) 𝓘(ℂ,ComplexModel n) ∞
      (windowProjection X r O) :=
  isSubmersion_composition (X := X) (Y := finiteProductAmbient X r)
    (Z := CMfd.of (n := n+r) O)
    (HironakaAuxiliaryGraphGeometry.isSubmersion_fst (n := n) (m := r)
      (X := X) (Y := ComplexModel r))
    (isSubmersion_val O)

private theorem window_power (Q : MarkedIdeal n X) (hQ : Q.ideal.IsCoherent)
    (O : Opens (finiteProductAmbient X r)) (e : ℕ) :
    windowRecord (powerMarked Q e) r O = powerMarked (windowRecord Q r O) e := by
  apply MarkedIdealOperationsTransform.MarkedIdeal.ext_of
  · rfl
  · rfl
  · exact pullback_idealPow (window_isSubmersion X r O).contMDiff hQ e
  · rfl

/-- No caller dictionary: finite plain product + actual open restriction
supply the entire pulled native state, then real common powers. -/
theorem window_native_data (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q)
    (hE : Q.E=[]) {W : Set X} {H : ℕ → ℕ} (hState : NativeHSState Q W H)
    (O : Opens (finiteProductAmbient X r))
    (J : MarkedIdeal (n+r) (CMfd.of (n := n+r) O)) (hJ : IsInvDomain (n+r) J)
    (hJE : J.E=[]) (hJState : NativeHSState J ((windowProjection X r O) ⁻¹' W) (finiteProductHS r H)) :
    IsInvDomain (n+r) (windowRecord Q r O) ∧
    NativeHSState (windowRecord Q r O) ((windowProjection X r O) ⁻¹' W) (finiteProductHS r H) ∧
    LocWPEquiv (windowRecord Q r O) J ∧
    windowRecord (powerMarked Q J.d) r O=powerMarked (windowRecord Q r O) J.d ∧
    IsInvDomain (n+r) (powerMarked (windowRecord Q r O) J.d) ∧
    IsInvDomain (n+r) (powerMarked J Q.d) ∧
    LocWPEquiv (powerMarked (windowRecord Q r O) J.d) (powerMarked J Q.d) ∧
    (powerMarked (windowRecord Q r O) J.d).d=(powerMarked J Q.d).d := by
  have hP:=original_ambient_domain_pullback (Y := CMfd.of (n := n+r) O) (window_isSubmersion X r O) Q hQ
  have heq : windowRecord Q r O =
      MarkedIdeal.pullback (Subtype.val : O → finiteProductAmbient X r) (finiteProductRecord r Q) :=
    whole_markedPullback_comp
      (ProductComplexManifold.contMDiff_fst (n := n) (m := r) (X := X) (Y := ComplexModel r))
      contMDiff_subtype_val Q hQ.isWellFormed.isCoherent
  have hPState : NativeHSState (windowRecord Q r O)
      ((windowProjection X r O) ⁻¹' W) (finiteProductHS r H) := by
    rw [heq]
    exact (native_state_finiteProduct r hState hE).restrict O
  have hPE : (windowRecord Q r O).E=[] := by
    change Q.E.map ((windowProjection X r O) ⁻¹' ·)=[]
    rw [hE];rfl
  have hL:=locWPEquiv_native hPState hJState (hJE.trans hPE.symm)
  have hCommon:=locEquiv_commonMark (κ := Kinds.wp) rfl hL hP hJ
  exact ⟨hP,hPState,hL,window_power Q hQ.isWellFormed.isCoherent O J.d,
    powerMarked_isInvDomain _ hP hJ.one_le_d,powerMarked_isInvDomain _ hJ hQ.one_le_d,hCommon⟩

private theorem empty_initial_normalized_exponents {m : ℕ} {A : CMfd.{0} m}
    (P Q : MarkedIdeal m A) (hE : P.E=[]) :
    ∀ H∈P.E,∀x∈P.cosupp,x∈H →
      Q.d*DivisorExponentAlong.divExpAlong m P.N P.ideal H x=
        P.d*DivisorExponentAlong.divExpAlong m Q.N Q.ideal H x := by
  intro H hH
  rw [hE] at hH
  exact (List.not_mem_nil hH).elim

/-- The independent actual J becomes canonical on the SAME whole actual
Cartesian tower; full values are compared only after TRUE common powers. -/
theorem window_canonical_comparison (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q)
    (hE : Q.E=[]) {W : Set X} {H : ℕ → ℕ} (hState : NativeHSState Q W H)
    (O : Opens (finiteProductAmbient X r))
    (J : MarkedIdeal (n+r) (CMfd.of (n := n+r) O)) (hJ : IsInvDomain (n+r) J)
    (hJE : J.E=[]) (hJState : NativeHSState J ((windowProjection X r O) ⁻¹' W) (finiteProductHS r H))
    {D : CMfd.{0} n} {D' : CMfd.{0} (n+r)}
    (T : BlowupTower X D) (S : BlowupTower (CMfd.of (n := n+r) O) D') (g : D' → D)
    (hp : IsActualTowerPullback (windowProjection X r O) S T g)
    (hCan : IsCanonical Q ((canonicalInvariant n).inv Q) T) :
    IsCanonical J ((canonicalInvariant (n+r)).inv J) S ∧
    (geoTransformAlong J S).cosupp=g ⁻¹' (geoTransformAlong Q T).cosupp ∧
    geoTransformAlong (windowRecord Q r O) S=markedPullback g (geoTransformAlong Q T) ∧
    ∀z,g z∈(geoTransformAlong Q T).cosupp →
      (canonicalInvariant (n+r)).inv (powerMarked J Q.d) S z=
        ambientDimensionMap (Nat.le_add_right n r)
          ((canonicalInvariant n).inv (powerMarked Q J.d) T (g z)) := by
  obtain ⟨hP,hPState,hL,hPower,hPPow,hJPow,hLPow,hMarks⟩:=
    window_native_data Q hQ hE hState O J hJ hJE hJState
  have hPE : (windowRecord Q r O).E=[] := by
    change Q.E.map ((windowProjection X r O) ⁻¹' ·)=[]
    rw [hE];rfl
  have hN : (windowRecord Q r O).N=J.N:=hPState.2.2.1.trans hJState.2.2.1.symm
  have hPCan:=IsActualTowerPullback.original_ambient_canonical hp Q hQ hCan
  have hJCan:=(canonicalInvariant_isCanonical_iff_of_local _ J hP hJ hL
    (SameCarrierDim.of_N_eq hN) (empty_initial_normalized_exponents _ J hPE) S).mp hPCan
  have hT:=(canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hQ T hCan
  have hS:=(canonicalInvariant (n+r)).isInvValue.isGeoTestTower_of_isCanonical hP S hPCan
  have hCos : (geoTransformAlong J S).cosupp=g ⁻¹' (geoTransformAlong Q T).cosupp:=
    ((hL.wEquiv.2 S).2 hS).symm.trans (HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_cosupport_dictionary hp Q hQ.isWellFormed hT)
  refine ⟨hJCan,hCos,(HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_marked_dictionary hp Q hQ.isWellFormed hT).2,?_⟩
  intro z hz
  have hQPow:=powerMarked_isInvDomain Q hQ hJ.one_le_d
  have hQPowCan:=(canonicalInvariant_isCanonical_power_iff Q hQ J.d hJ.one_le_d T).mp hCan
  have hPPowCan : IsCanonical (powerMarked (windowRecord Q r O) J.d)
      ((canonicalInvariant (n+r)).inv (powerMarked (windowRecord Q r O) J.d)) S := by
    rw [←hPower]
    exact IsActualTowerPullback.original_ambient_canonical hp _ hQPow hQPowCan
  have hPowCos:=((locEquiv_powerMarked (κ := Kinds.wp) rfl Q hQ hJ.one_le_d).wEquiv.2 T).2 hT
  have hzPow : g z∈(geoTransformAlong (powerMarked Q J.d) T).cosupp:=hPowCos ▸ hz
  have hPowT:=(canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hQPow T hQPowCan
  have hzP : z∈(geoTransformAlong (powerMarked (windowRecord Q r O) J.d) S).cosupp:=by
    rw [←hPower]
    change z∈(geoTransformAlong (markedPullback (windowProjection X r O) (powerMarked Q J.d)) S).cosupp
    rw [HironakaSmoothSubmersionRelativeControlledTower.IsActualTowerPullback.relative_cosupport_dictionary hp _ hQPow.isWellFormed hPowT]
    exact hzPow
  have hValue:=(classFunctorialFor_canonicalInvariant (n+r)).inv_eq _ _ hPPow hJPow hLPow hMarks
    (by change (windowRecord Q r O).E=J.E;exact hPE.trans hJE.symm)
    (SameCarrierDim.of_N_eq hN) (expAgree_of_nil hPE) S hPPowCan z hzP
  have hSmooth:=IsActualTowerPullback.original_ambient_value hp _ hQPow hQPowCan z hzPow
  change (canonicalInvariant (n+r)).inv (windowRecord (powerMarked Q J.d) r O) S z=_ at hSmooth
  rw [hPower] at hSmooth
  exact hValue.symm.trans hSmooth

/-- Genuine local visible-maximum alternative, including empty windows.
The actual source values are embedded FIRST; no inverse order map exists. -/
theorem window_maxLocus_eq_or (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q)
    (hE : Q.E=[]) {W : Set X} {H : ℕ → ℕ} (hState : NativeHSState Q W H)
    (O : Opens (finiteProductAmbient X r))
    (J : MarkedIdeal (n+r) (CMfd.of (n := n+r) O)) (hJ : IsInvDomain (n+r) J)
    (hJE : J.E=[]) (hJState : NativeHSState J ((windowProjection X r O) ⁻¹' W) (finiteProductHS r H))
    {D : CMfd.{0} n} {D' : CMfd.{0} (n+r)}
    (T : BlowupTower X D) (S : BlowupTower (CMfd.of (n := n+r) O) D') (g : D' → D)
    (hp : IsActualTowerPullback (windowProjection X r O) S T g)
    (hCan : IsCanonical Q ((canonicalInvariant n).inv Q) T) :
    g ⁻¹' maxLocus ((canonicalInvariant n).inv Q T) (geoTransformAlong Q T).cosupp=∅ ∨
      g ⁻¹' maxLocus ((canonicalInvariant n).inv Q T) (geoTransformAlong Q T).cosupp=
        maxLocus ((canonicalInvariant (n+r)).inv J S) (geoTransformAlong J S).cosupp := by
  obtain ⟨hJCan,hCos,_,hValue⟩:=window_canonical_comparison Q hQ hE hState O J hJ hJE hJState T S g hp hCan
  have hT:=(canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hQ T hCan
  have hS:=(canonicalInvariant (n+r)).isInvValue.isGeoTestTower_of_isCanonical hJ S hJCan
  have hQCos:=((locEquiv_powerMarked (κ := Kinds.wp) rfl Q hQ hJ.one_le_d).wEquiv.2 T).2 hT
  have hJCos:=((locEquiv_powerMarked (κ := Kinds.wp) rfl J hJ hQ.one_le_d).wEquiv.2 S).2 hS
  have hNormCos : (geoTransformAlong (powerMarked J Q.d) S).cosupp=
      g ⁻¹' (geoTransformAlong (powerMarked Q J.d) T).cosupp:=by
    rw [←hJCos,←hQCos];exact hCos
  have hAlt:=MaxLocusLocal.preimage_maxLocus_eq_or_of_eq
    (f := ambientDimensionMap (Nat.le_add_right n r) ∘ (canonicalInvariant n).inv (powerMarked Q J.d) T)
    (g := (canonicalInvariant (n+r)).inv (powerMarked J Q.d) S)
    (s := (geoTransformAlong (powerMarked Q J.d) T).cosupp) g (by
      intro z hz
      exact (hValue z (hQCos.symm ▸ hz)).symm)
  rw [MaxLocusLocal.maxLocus_comp_strictMono (strictMono_ambientDimensionMap (Nat.le_add_right n r)),
    ←hNormCos,←canonicalInvariant_maxLocus_power Q hQ J.d hJ.one_le_d T hCan,
    ←canonicalInvariant_maxLocus_power J hJ Q.d hQ.one_le_d S hJCan] at hAlt
  exact hAlt

/-- If the genuine window projection is surjective, its actual final map
is surjective and the visible-maximum alternative becomes full equality. -/
theorem window_maxLocus_eq_of_surjective (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q)
    (hE : Q.E=[]) {W : Set X} {H : ℕ → ℕ} (hState : NativeHSState Q W H)
    (O : Opens (finiteProductAmbient X r))
    (J : MarkedIdeal (n+r) (CMfd.of (n := n+r) O)) (hJ : IsInvDomain (n+r) J)
    (hJE : J.E=[]) (hJState : NativeHSState J ((windowProjection X r O) ⁻¹' W) (finiteProductHS r H))
    {D : CMfd.{0} n} {D' : CMfd.{0} (n+r)}
    (T : BlowupTower X D) (S : BlowupTower (CMfd.of (n := n+r) O) D') (g : D' → D)
    (hp : IsActualTowerPullback (windowProjection X r O) S T g)
    (hSurj : Function.Surjective (windowProjection X r O))
    (hCan : IsCanonical Q ((canonicalInvariant n).inv Q) T) :
    g ⁻¹' maxLocus ((canonicalInvariant n).inv Q T) (geoTransformAlong Q T).cosupp=
      maxLocus ((canonicalInvariant (n+r)).inv J S) (geoTransformAlong J S).cosupp := by
  obtain ⟨hJCan,hCos,_,hValue⟩:=window_canonical_comparison Q hQ hE hState O J hJ hJE hJState T S g hp hCan
  have hT:=(canonicalInvariant n).isInvValue.isGeoTestTower_of_isCanonical hQ T hCan
  have hS:=(canonicalInvariant (n+r)).isInvValue.isGeoTestTower_of_isCanonical hJ S hJCan
  have hQCos:=((locEquiv_powerMarked (κ := Kinds.wp) rfl Q hQ hJ.one_le_d).wEquiv.2 T).2 hT
  have hJCos:=((locEquiv_powerMarked (κ := Kinds.wp) rfl J hJ hQ.one_le_d).wEquiv.2 S).2 hS
  rw [canonicalInvariant_maxLocus_power Q hQ J.d hJ.one_le_d T hCan,
    canonicalInvariant_maxLocus_power J hJ Q.d hQ.one_le_d S hJCan]
  have hStrict:=strictMono_ambientDimensionMap (Nat.le_add_right n r)
  have hto : ∀y,y∈(geoTransformAlong J S).cosupp → g y∈(geoTransformAlong Q T).cosupp:=
    fun y hy=>(Set.ext_iff.mp hCos y).mp hy
  have hback : ∀y,g y∈(geoTransformAlong Q T).cosupp → y∈(geoTransformAlong J S).cosupp:=
    fun y hy=>(Set.ext_iff.mp hCos y).mpr hy
  ext z
  constructor
  · rintro ⟨hz,hzMax⟩
    have hzQ : g z∈(geoTransformAlong Q T).cosupp:=hQCos.symm ▸ hz
    refine ⟨hJCos ▸ hback z hzQ,?_⟩
    intro y hy
    have hyQ : g y∈(geoTransformAlong Q T).cosupp:=hto y (hJCos.symm ▸ hy)
    rw [hValue z hzQ,hValue y hyQ]
    exact hStrict.monotone (hzMax (g y) (hQCos ▸ hyQ))
  · rintro ⟨hz,hzMax⟩
    have hzQ : g z∈(geoTransformAlong Q T).cosupp:=hto z (hJCos.symm ▸ hz)
    refine ⟨hQCos ▸ hzQ,?_⟩
    intro y hy
    obtain ⟨w,rfl⟩:=hp.surjective hSurj y
    have hwQ : g w∈(geoTransformAlong Q T).cosupp:=hQCos.symm ▸ hy
    have hw : w∈(geoTransformAlong (powerMarked J Q.d) S).cosupp:=hJCos ▸ hback w hwQ
    have hLe:=hzMax w hw
    rw [hValue z hzQ,hValue w hwQ] at hLe
    exact hStrict.le_iff_le.mp hLe

/-- A genuine own-native source history is CONSTRUCTED, not supplied. -/
theorem exists_window_native_canonical_history (Q : MarkedIdeal n X) (hQ : IsInvDomain n Q)
    (hE : Q.E=[]) {W : Set X} {H : ℕ → ℕ} (hState : NativeHSState Q W H)
    (O : Opens (finiteProductAmbient X r))
    (J : MarkedIdeal (n+r) (CMfd.of (n := n+r) O)) (hJ : IsInvDomain (n+r) J)
    (hJE : J.E=[]) (hJState : NativeHSState J ((windowProjection X r O) ⁻¹' W) (finiteProductHS r H))
    {D : CMfd.{0} n} (T : BlowupTower X D)
    (hCan : IsCanonical Q ((canonicalInvariant n).inv Q) T) :
    ∃(D' : CMfd.{0} (n+r))(S : BlowupTower (CMfd.of (n := n+r) O) D')(g : D' → D),
      IsActualTowerPullback (windowProjection X r O) S T g ∧ S.length=T.length ∧
      (∀z,T.proj (g z)=windowProjection X r O (S.proj z)) ∧
      HironakaSmoothSubmersionOrderedChoiceBaseChange.HolomorphicSquarePullback (windowProjection X r O) g S.proj T.proj ∧
      IsCanonical J ((canonicalInvariant (n+r)).inv J) S ∧
      (geoTransformAlong J S).cosupp=g ⁻¹' (geoTransformAlong Q T).cosupp ∧
      geoTransformAlong (windowRecord Q r O) S=markedPullback g (geoTransformAlong Q T) ∧
      (∀z,g z∈(geoTransformAlong Q T).cosupp →
        (canonicalInvariant (n+r)).inv (powerMarked J Q.d) S z=
          ambientDimensionMap (Nat.le_add_right n r)
            ((canonicalInvariant n).inv (powerMarked Q J.d) T (g z))) ∧
      (g ⁻¹' maxLocus ((canonicalInvariant n).inv Q T) (geoTransformAlong Q T).cosupp=∅ ∨
        g ⁻¹' maxLocus ((canonicalInvariant n).inv Q T) (geoTransformAlong Q T).cosupp=
          maxLocus ((canonicalInvariant (n+r)).inv J S) (geoTransformAlong J S).cosupp) := by
  obtain ⟨D',S,g,hp⟩:=exists_actual_tower (Y := CMfd.of (n := n+r) O) (window_isSubmersion X r O) T
  obtain ⟨hJCan,hCos,hRecord,hValue⟩:=window_canonical_comparison Q hQ hE hState O J hJ hJE hJState T S g hp hCan
  exact ⟨D',S,g,hp,hp.length_eq,hp.proj_comm,hp.universal,hJCan,hCos,hRecord,hValue,
    window_maxLocus_eq_or Q hQ hE hState O J hJ hJE hJState T S g hp hCan⟩

end
end Hironaka.HironakaG1NativeProductCanonicalComparison
