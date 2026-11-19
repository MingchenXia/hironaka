import Hironaka.Analytic.Unibranch.HironakaG11CompatibleAnalyticCover
import Hironaka.Analytic.Unibranch.EmbeddedBlowupGlobalUniversalLocal
import Hironaka.Analytic.Unibranch.EmbeddedBlowupParacompact
import Hironaka.Resolution.HironakaSingularRankOneLocalGenerators
import Hironaka.Resolution.HironakaSingularSubspaceBlowupCartierUniversalStalkTransport
import Hironaka.Resolution.HironakaIntrinsicReducedCentreOpenPullback
import Hironaka.Resolution.HironakaIntrinsicMorphismGluingAnalytic

/-!
# Locality of ideal blowups along open immersions (goal G11, route step 5 bridge)

The global G11 sequence is glued from LOCAL canonical histories. To compare them one needs that a
blowup is local on the base: over an open subspace `j : W ⟶ X`, the blowup `p : Y ⟶ X` of the
reduced ideal of `C ⊆ X` restricts to the blowup of the reduced ideal of the trace `j⁻¹ C`. This
file proves this for the intrinsic ideal-blowup predicate `IsIdealBlowup` (own rank-one data and the
universal property among ALL original complex spaces).

* `hasRankOneData_iff`: standard rank-one local-free data of a pulled ideal are the same as LOCAL
  REGULAR PRINCIPAL GENERATION (`HasLocalRegularGenerators`): every point has a neighbourhood and a
  function whose germs generate the pulled stalk ideals and are non-zero-divisors there. The new
  direction is `exists_regular_generator_of_hasRankOneData` (the unique generating section of a
  local-free chart and the local unit isomorphism on the original stalks).
* Consequences: rank-one data restrict along open immersions (`hasRankOneData_comp_openImmersion`);
  pulling the reduced ideal of `C` back along `q ≫ j` (`j` an open immersion) or that of `j⁻¹ C`
  along `q` gives the same stalk ideals (`stalkIdeal_comp_openImmersion`), hence the same rank-one
  condition (`hasRankOneData_comp_openImmersion_iff`).
* Open subspaces of original complex spaces (`openSubspace`, `openSubspaceInclusion`) on
  PARACOMPACT open sets; the local model clause is derived (`charts_of_openImmersion`), and the
  preimage of an open subspace under a proper map is paracompact
  (`paracompactSpace_preimage_range`).
* **Locality** (`exists_openImmersion_of_isIdealBlowup`): for a proper ideal blowup `p` of `C`, an
  open immersion `j : W ⟶ X` and an ideal blowup `p_W : Y_W ⟶ W` of `j⁻¹ C`, there is a unique
  `L : Y_W ⟶ Y` with `L ≫ p = p_W ≫ j`, and it is an open immersion onto `p⁻¹ (range j)`;
  the smooth-centre form is `exists_openImmersion_of_isSmoothCentreBlowup`.

No compactness, global embedding, countability or resolution hypothesis is used.
Blueprint: `hironaka-g11-resume-blowup-locality.tex`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG11BlowupLocality

open Hironaka HironakaSingularModuleSheafStalk HironakaSingularLocallyFreeStalk
  HironakaSingularRankOneLocalGenerators HironakaNativePulledIdealSheaf HironakaNativePulledIdealStalk
  HironakaIntrinsicReducedCentreIdealSheaf HironakaIntrinsicReducedCentreOpenPullback
  HironakaSingularSubspaceBlowupCartierUniversalStalkTransport
  SmoothCentreModification

noncomputable section

/-! ### Rank-one data is local principal generation by regular sections -/

section RankOne

variable {A : LocallyRingedSpace.{0}}

/-- **Rank-one data give local regular generators.** If a module subsheaf of `𝒪_A` (an injective
`f : N ⟶ 𝒪_A`) has standard rank-one local-free data, every point has a neighbourhood `U` and
a section `t` of `N` over `U` whose image generates the stalk image at every point of `U` and is
a non-zero-divisor there. -/
theorem exists_regular_generator_of_hasRankOneData
    {N : SheafOfModules.{0} (forgetRing A.toSheafedSpace.sheaf)}
    (f : N ⟶ SheafOfModules.unit (forgetRing A.toSheafedSpace.sheaf))
    (hf : ∀ V : Opens A.toTopCat, Function.Injective (f.val.app (op V)))
    (h : HasRankOneData N) (x : A) :
    ∃ (U : Opens A.toTopCat) (_ : x ∈ U) (t : N.val.obj (op U)),
      ∀ (y : A) (hy : y ∈ U),
        LinearMap.range (stalkInclusionLinearMap A.toSheafedSpace.sheaf N f y) =
          Ideal.span {A.presheaf.germ U y hy (f.val.app (op U) t)} ∧
        IsRegular (A.presheaf.germ U y hy (f.val.app (op U) t)) := by
  classical
  obtain ⟨q, hq, huniq⟩ := h
  let R := A.toSheafedSpace.sheaf
  obtain ⟨V, g, hV, hxV⟩ :=
    (Opens.mem_grothendieckTopology A.toTopCat).mp (q.coversTop ⊤) x (by trivial)
  obtain ⟨i, ⟨g'⟩⟩ := (Sieve.mem_ofObjects_iff q.X g).mp hV
  have hxU : x ∈ q.X i := g'.le hxV
  let U := q.X i
  let σ := q.generators i
  let : Unique σ.I := Classical.choice (huniq i)
  let d : σ.I := default
  let s₀ := σ.s d
  let t : N.val.obj (op U) := s₀.val (op (Over.mk (𝟙 U)))
  have hs : (N.over U).unitHomEquiv (localUnitMap R U t) = s₀ := by
    apply PresheafOfModules.sections_ext
    intro W
    rw [SheafOfModules.unitHomEquiv_apply_coe, localUnitMap_app, one_smul]
    exact s₀.property (Over.homMk W.unop.hom : W.unop ⟶ Over.mk (𝟙 U)).op
  have hg : SheafOfModules.ιFree d ≫ σ.π = localUnitMap R U t := by
    rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, Equiv.apply_symm_apply,
      Equiv.symm_apply_eq]
    exact hs.symm
  have hiso : IsIso (localUnitMap R U t) := by
    rw [← hg]
    have : IsIso (SheafOfModules.ιFree (R := (forgetRing R).over U) d) := by
      have h := coproductUniqueIso_inv (fun _ : σ.I => SheafOfModules.unit ((forgetRing R).over U))
      change IsIso (Sigma.ι (fun _ : σ.I => SheafOfModules.unit ((forgetRing R).over U)) d)
      rw [← h]
      infer_instance
    have : IsIso σ.π := SheafOfModules.LocalGeneratorsData.IsLocallyFreeData.isIso (q := q) i
    infer_instance
  refine ⟨U, hxU, t, ?_⟩
  intro y hy
  let k := (stalkLinearMapOfOver R (M := SheafOfModules.unit (forgetRing R))
    U (localUnitMap R U t) y hy).comp (unitStalkLinearEquiv R y).symm.toLinearMap
  let a : ↑(TopCat.Presheaf.stalk R.obj y) := TopCat.Presheaf.germ R.obj U y hy (f.val.app (op U) t)
  have hformula (r : ↑(TopCat.Presheaf.stalk R.obj y)) :
      stalkInclusionLinearMap R N f y (k r) = r * a := by
    change stalkInclusionLinearMap R N f y
      (stalkLinearMapOfOver R (M := SheafOfModules.unit (forgetRing R)) U (localUnitMap R U t) y hy
        ((unitStalkLinearEquiv R y).symm r)) = r * a
    rw [localUnitMap_stalk, map_smul, stalkInclusionLinearMap_germ]
    rfl
  have hk : Function.Bijective k := by
    let e : (SheafOfModules.unit (forgetRing R)).over U ≅ N.over U :=
      { hom := localUnitMap R U t
        inv := inv (localUnitMap R U t)
        hom_inv_id := IsIso.hom_inv_id _
        inv_hom_id := IsIso.inv_hom_id _ }
    have hb : Function.Bijective (stalkLinearMapOfOver R (M := SheafOfModules.unit (forgetRing R))
        U (localUnitMap R U t) y hy) :=
      (stalkLinearEquivOfOverIso R U e y hy).bijective
    exact hb.comp (unitStalkLinearEquiv R y).symm.bijective
  have hinj := stalkInclusionLinearMap_injective R N f hf y
  change LinearMap.range (stalkInclusionLinearMap R N f y) = Ideal.span {a} ∧ IsRegular a
  constructor
  · apply le_antisymm
    · rintro _ ⟨m, rfl⟩
      obtain ⟨r, rfl⟩ := hk.2 m
      rw [hformula]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_singleton a))
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      refine ⟨k 1, ?_⟩
      rw [hformula, one_mul]
  · have hl : IsLeftRegular a := by
      intro r s hrs
      change a * r = a * s at hrs
      apply hk.1
      apply hinj
      rw [hformula, hformula, mul_comm r, mul_comm s]
      exact hrs
    exact ⟨hl, hl.right_of_commute (fun _ => mul_comm _ _)⟩

variable {X : LocallyRingedSpace.{0}}

/-- **Local regular principal generation** of the pulled ideal of `B` along `F`: every point
has a neighbourhood `U` and a function on `U` whose germ generates the pulled stalk ideal and
is a non-zero-divisor at every point of `U` (the pulled ideal is a Cartier divisor). -/
def HasLocalRegularGenerators (F : A ⟶ X)
    (B : SheafOfModules.{0} (forgetRing X.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing X.toSheafedSpace.sheaf)) : Prop :=
  ∀ x : A, ∃ (U : Opens A.toTopCat) (_ : x ∈ U) (s : (A.presheaf.obj (op U)).carrier),
    ∀ (y : A) (hy : y ∈ U),
      nativePulledIdealStalkIdeal F B b y = Ideal.span {A.presheaf.germ U y hy s} ∧
        IsRegular (A.presheaf.germ U y hy s)

/-- **Rank-one data of a pulled ideal is local regular principal generation.** -/
theorem hasRankOneData_iff (F : A ⟶ X)
    (B : SheafOfModules.{0} (forgetRing X.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing X.toSheafedSpace.sheaf)) :
    HasRankOneData (nativePulledIdealModule F B b) ↔ HasLocalRegularGenerators F B b := by
  constructor
  · intro h x
    obtain ⟨U, hxU, t, ht⟩ := exists_regular_generator_of_hasRankOneData
      (nativePulledIdealInclusion F B b) (fun _ => Subtype.val_injective) h x
    refine ⟨U, hxU, (nativePulledIdealInclusion F B b).val.app (op U) t, fun y hy => ?_⟩
    obtain ⟨h1, h2⟩ := ht y hy
    exact ⟨(nativePulledIdealStalkInclusion_range F B b y).symm.trans h1, h2⟩
  · intro h
    classical
    have key : ∀ x : A, ∃ (U : Opens A.toTopCat) (_ : x ∈ U)
        (s : nativePulledIdealSectionIdeal F B b U), ∀ (y : A) (hy : y ∈ U),
          nativePulledIdealStalkIdeal F B b y = Ideal.span {A.presheaf.germ U y hy s.val} ∧
            IsRegular (A.presheaf.germ U y hy s.val) := by
      intro x
      obtain ⟨U, hxU, s, hs⟩ := h x
      refine ⟨U, hxU, ⟨s, fun y hy => ?_⟩, hs⟩
      rw [(hs y hy).1]
      exact Ideal.subset_span (Set.mem_singleton _)
    choose U hxU s hs using key
    exact exists_locallyFreeData_of_regular_sections A.toSheafedSpace.sheaf
      (nativePulledIdealInclusion F B b) (fun _ => Subtype.val_injective)
      U (fun x => ⟨x, hxU x⟩) s (fun i y hy => (hs i y hy).2)
      (fun i y hy => (nativePulledIdealStalkInclusion_range F B b y).trans (hs i y hy).1)

/-- Local regular generation only depends on the pulled stalk ideals. -/
theorem hasLocalRegularGenerators_congr {X' : LocallyRingedSpace.{0}} {F : A ⟶ X}
    {B : SheafOfModules.{0} (forgetRing X.toSheafedSpace.sheaf)}
    {b : B ⟶ SheafOfModules.unit (forgetRing X.toSheafedSpace.sheaf)} {F' : A ⟶ X'}
    {B' : SheafOfModules.{0} (forgetRing X'.toSheafedSpace.sheaf)}
    {b' : B' ⟶ SheafOfModules.unit (forgetRing X'.toSheafedSpace.sheaf)}
    (h : ∀ y, nativePulledIdealStalkIdeal F B b y = nativePulledIdealStalkIdeal F' B' b' y) :
    HasLocalRegularGenerators F B b ↔ HasLocalRegularGenerators F' B' b' := by
  unfold HasLocalRegularGenerators
  simp only [h]

/-- **Restriction to an open subspace.** Local regular generation of a pulled ideal restricts
along an open immersion (sections restrict, stalk maps are ring isomorphisms). -/
theorem HasLocalRegularGenerators.comp_openImmersion {A' : LocallyRingedSpace.{0}}
    (ι : A' ⟶ A) [LocallyRingedSpace.IsOpenImmersion ι] {F : A ⟶ X}
    {B : SheafOfModules.{0} (forgetRing X.toSheafedSpace.sheaf)}
    {b : B ⟶ SheafOfModules.unit (forgetRing X.toSheafedSpace.sheaf)}
    (h : HasLocalRegularGenerators F B b) : HasLocalRegularGenerators (ι ≫ F) B b := by
  intro z
  obtain ⟨U, hzU, s, hs⟩ := h (ι.base z)
  refine ⟨(Opens.map ι.base).obj U, hzU, ι.c.app (op U) s, fun y hy => ?_⟩
  obtain ⟨hspan, hreg⟩ := hs (ι.base y) hy
  let e := (asIso (ι.stalkMap y)).commRingCatIsoToRingEquiv
  have hgerm : A'.presheaf.germ ((Opens.map ι.base).obj U) y hy (ι.c.app (op U) s) =
      e (A.presheaf.germ U (ι.base y) hy s) :=
    (LocallyRingedSpace.stalkMap_germ_apply ι U y hy s).symm
  rw [EmbeddedBlowupGlobalUniversalLocal.nativePulledIdealStalkIdeal_comp ι F B b y, hspan,
    Ideal.map_span, Set.image_singleton, hgerm]
  exact ⟨rfl, isRegular_map_ringEquiv e hreg⟩

/-- Rank-one data of a pulled ideal restricts along open immersions. -/
theorem hasRankOneData_comp_openImmersion {A' : LocallyRingedSpace.{0}}
    (ι : A' ⟶ A) [LocallyRingedSpace.IsOpenImmersion ι] (F : A ⟶ X)
    (B : SheafOfModules.{0} (forgetRing X.toSheafedSpace.sheaf))
    (b : B ⟶ SheafOfModules.unit (forgetRing X.toSheafedSpace.sheaf))
    (h : HasRankOneData (nativePulledIdealModule F B b)) :
    HasRankOneData (nativePulledIdealModule (ι ≫ F) B b) :=
  (hasRankOneData_iff (ι ≫ F) B b).mpr (((hasRankOneData_iff F B b).mp h).comp_openImmersion ι)

/-- **The pulled centre ideal through an open immersion.** Pulling the reduced ideal of `C ⊆ X`
back along `q ≫ j` (`j` an open immersion) gives the same stalk ideals as pulling the reduced
ideal of the trace `j⁻¹ C ⊆ W` back along `q`. -/
theorem stalkIdeal_comp_openImmersion {T W : LocallyRingedSpace.{0}} (q : T ⟶ W) (j : W ⟶ X)
    [LocallyRingedSpace.IsOpenImmersion j] (C : Set X) (y : T) :
    nativePulledIdealStalkIdeal (q ≫ j) (intrinsicReducedCentreIdealModule X C)
        (intrinsicReducedCentreIdealInclusion X C) y =
      nativePulledIdealStalkIdeal q (intrinsicReducedCentreIdealModule W (j.base ⁻¹' C))
        (intrinsicReducedCentreIdealInclusion W (j.base ⁻¹' C)) y := by
  rw [EmbeddedBlowupGlobalUniversalLocal.nativePulledIdealStalkIdeal_comp q j _ _ y,
    openImmersion_pulled_stalkIdeal_eq j C (q.base y)]
  rfl

/-- **Rank-one data through an open immersion.** The pulled reduced ideal of `C` along `q ≫ j`
has rank-one data iff the pulled reduced ideal of `j⁻¹ C` along `q` has. -/
theorem hasRankOneData_comp_openImmersion_iff {T W : LocallyRingedSpace.{0}} (q : T ⟶ W)
    (j : W ⟶ X) [LocallyRingedSpace.IsOpenImmersion j] (C : Set X) :
    HasRankOneData (nativePulledIdealModule (q ≫ j) (intrinsicReducedCentreIdealModule X C)
        (intrinsicReducedCentreIdealInclusion X C)) ↔
      HasRankOneData (nativePulledIdealModule q
        (intrinsicReducedCentreIdealModule W (j.base ⁻¹' C))
        (intrinsicReducedCentreIdealInclusion W (j.base ⁻¹' C))) := by
  rw [hasRankOneData_iff, hasRankOneData_iff]
  exact hasLocalRegularGenerators_congr (stalkIdeal_comp_openImmersion q j C)

end RankOne

/-! ### Open subspaces of original complex spaces -/

section OpenSubspace

open Hironaka HironakaReducedComplexAnalyticSpaces
  HironakaActualAnalyticSubspace HironakaActualAnalyticSubspaceMaps
  HironakaActualAnalyticSubspaceOpenRestriction HironakaResolutionSpaceComplex

/-- The local analytic-model clause passes through an open immersion over the complex point
(the chart part of `hasAnalyticCharts_of_openImmersion`, without any countability). -/
theorem charts_of_openImmersion {H T : LocallyRingedSpace}
    (σH : H ⟶ complexPoint) (σT : T ⟶ complexPoint)
    (hT : ∀ x : T, ∃ (n : ℕ) (U : Opens (ComplexModel n)) (C : Set U),
      IsComplexAnalyticSubset (n := n) C ∧
      ∃ i : (modelOver U C).left ⟶ T,
        LocallyRingedSpace.IsOpenImmersion i ∧ i ≫ σT = (modelOver U C).hom ∧ x ∈ range i.base)
    (j : H ⟶ T) [hj : LocallyRingedSpace.IsOpenImmersion j] (hjp : j ≫ σT = σH) :
    ∀ x : H, ∃ (n : ℕ) (U : Opens (ComplexModel n)) (C : Set U),
      IsComplexAnalyticSubset (n := n) C ∧
      ∃ i : (modelOver U C).left ⟶ H,
        LocallyRingedSpace.IsOpenImmersion i ∧ i ≫ σH = (modelOver U C).hom ∧
          x ∈ range i.base := by
  intro x
  obtain ⟨n, V, C, hC, i, hi, hip, c, hcx⟩ := hT (j.base x)
  change i ≫ σT = subspacePointMap (n := n) C at hip
  let : LocallyRingedSpace.IsOpenImmersion i := hi
  let Q : Opens (TopCat.of C) :=
    ⟨i.base ⁻¹' range j.base, hj.base_open.isOpen_range.preimage i.base.hom.continuous⟩
  obtain ⟨O, hO, hOQ⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp Q.isOpen
  let A : Opens V := ⟨O, hO⟩
  have hcA : c.val ∈ A := by
    change c ∈ Subtype.val ⁻¹' O
    rw [hOQ]
    change i.base c ∈ range j.base
    rw [hcx]
    exact ⟨x, rfl⟩
  let C' : Set A := (Subtype.val : A → V) ⁻¹' C
  let R := actualOpenSubspaceMap (n := n) C A ≫ i
  have : LocallyRingedSpace.IsOpenImmersion R := by
    dsimp [R]
    infer_instance
  have hR : range R.base ⊆ range j.base := by
    rintro _ ⟨y, rfl⟩
    have hy : (⟨y.val.val, y.property⟩ : C) ∈ Q := by
      change (⟨y.val.val, y.property⟩ : C) ∈ (Q : Set C)
      rw [← hOQ]
      exact y.val.property
    exact hy
  let L := LocallyRingedSpace.IsOpenImmersion.lift j R hR
  have hfac : L ≫ j = R := LocallyRingedSpace.IsOpenImmersion.lift_fac j R hR
  have : LocallyRingedSpace.IsOpenImmersion L := by
    let : IsIso (pullback.snd j R) :=
      LocallyRingedSpace.IsOpenImmersion.pullback_snd_isIso_of_range_subset j R hR
    dsimp [L, LocallyRingedSpace.IsOpenImmersion.lift]
    infer_instance
  have hLp : L ≫ σH = subspacePointMap (n := n) C' := by
    rw [← hjp, ← Category.assoc, hfac]
    dsimp [R]
    rw [Category.assoc, hip]
    exact actualSubspaceMap_point contMDiff_subtype_val (fun _ hy => hy)
  let c' : C' := ⟨⟨c.val, hcA⟩, c.property⟩
  have hLc : L.base c' = x := by
    apply hj.base_open.injective
    calc
      j.base (L.base c') = R.base c' := congrArg (fun f => f.base c') hfac
      _ = j.base x := hcx
  have hC' : IsComplexAnalyticSubset (n := n) C' :=
    AnalyticSubsetOpens.isComplexAnalyticSubset_preimage_val hC A
  obtain ⟨V', D, hD, k, hk, hkp, z, hzc⟩ := exists_model_chart hC' c'
  let : LocallyRingedSpace.IsOpenImmersion k := hk
  refine ⟨n, V', D, hD, k ≫ L, inferInstance, ?_, z, ?_⟩
  · rw [Category.assoc, hLp]
    exact hkp
  · change L.base (k.base z) = x
    rw [hzc, hLc]

/-- **The open subspace** of an original complex space on a PARACOMPACT open subset (the
literal locally ringed restriction; Hausdorffness and the local analytic models are derived). -/
@[implicit_reducible]
def openSubspace (Y : SourceReducedComplexSpace) (V : Opens Y.obj.left) [ParacompactSpace V] :
    SourceReducedComplexSpace := by
  let := Y.property.1
  let j := Y.obj.left.ofRestrict V.isOpenEmbedding
  refine ⟨Over.mk (j ≫ Y.obj.hom), ?_, ?_, ?_⟩
  · change T2Space V
    infer_instance
  · change ParacompactSpace V
    infer_instance
  · exact charts_of_openImmersion _ _ Y.property.2.2 j rfl

/-- The inclusion of an open subspace. -/
def openSubspaceInclusion (Y : SourceReducedComplexSpace) (V : Opens Y.obj.left)
    [ParacompactSpace V] : openSubspace Y V ⟶ Y :=
  ObjectProperty.homMk (Over.homMk (Y.obj.left.ofRestrict V.isOpenEmbedding) rfl)

instance openSubspaceInclusion_isOpenImmersion (Y : SourceReducedComplexSpace)
    (V : Opens Y.obj.left) [ParacompactSpace V] :
    LocallyRingedSpace.IsOpenImmersion (openSubspaceInclusion Y V).hom.left := by
  change LocallyRingedSpace.IsOpenImmersion (Y.obj.left.ofRestrict V.isOpenEmbedding)
  infer_instance

theorem range_openSubspaceInclusion (Y : SourceReducedComplexSpace) (V : Opens Y.obj.left)
    [ParacompactSpace V] :
    range (openSubspaceInclusion Y V).hom.left.base = (V : Set Y.obj.left) := by
  ext y
  constructor
  · rintro ⟨v, rfl⟩
    exact v.property
  · intro hy
    exact ⟨⟨y, hy⟩, rfl⟩

/-- **Paracompactness of preimages of open subspaces under proper maps.** For a proper map
`p : Y ⟶ X` and an open immersion `j : W ⟶ X` of original complex spaces, the open set
`p⁻¹ (range j)` is paracompact (it maps properly onto the paracompact space `W`). -/
theorem paracompactSpace_preimage_range {X Y W : SourceReducedComplexSpace} (p : Y ⟶ X)
    (hp : IsProperMap p.hom.left.base) (j : W ⟶ X)
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) :
    ParacompactSpace (p.hom.left.base ⁻¹' range j.hom.left.base) := by
  let : ParacompactSpace W.obj.left.toPresheafedSpace := W.property.2.1
  let e := hj.base_open.isEmbedding.toHomeomorph
  exact EmbeddedBlowupParacompact.paracompactSpace_of_isProperMap
    (e.symm ∘ (range j.hom.left.base).restrictPreimage p.hom.left.base)
    (e.symm.isProperMap.comp (hp.restrictPreimage _))

end OpenSubspace

/-! ### Locality of ideal blowups -/

section Locality

private theorem hom_ext_of_mono {A B : SourceReducedComplexSpace} {f g : A ⟶ B}
    (h : f.hom.left = g.hom.left) : f = g := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact h

/-- **Locality of the blowup along an open immersion.** Let `p : Y ⟶ X` be a proper ideal blowup
of the reduced ideal of `C ⊆ X`, `j : W ⟶ X` an open immersion, and `p_W : Y_W ⟶ W` an ideal
blowup of the reduced ideal of the trace `j⁻¹ C`. Then there is a UNIQUE `L : Y_W ⟶ Y` with
`L ≫ p = p_W ≫ j`; it is an open immersion onto `p⁻¹ (range j)`. -/
theorem exists_openImmersion_of_isIdealBlowup {X Y W YW : SourceReducedComplexSpace}
    {p : Y ⟶ X} {j : W ⟶ X} {pW : YW ⟶ W} (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
    {C : Set X.obj.left}
    (hp : IsIdealBlowup p (intrinsicReducedCentreIdealModule X.obj.left C)
      (intrinsicReducedCentreIdealInclusion X.obj.left C))
    (hprop : IsProperMap p.hom.left.base)
    (hpW : IsIdealBlowup pW (intrinsicReducedCentreIdealModule W.obj.left (j.hom.left.base ⁻¹' C))
      (intrinsicReducedCentreIdealInclusion W.obj.left (j.hom.left.base ⁻¹' C))) :
    ∃ L : YW ⟶ Y, (L ≫ p = pW ≫ j ∧ ∀ L₁ : YW ⟶ Y, L₁ ≫ p = pW ≫ j → L₁ = L) ∧
      LocallyRingedSpace.IsOpenImmersion L.hom.left ∧
      range L.hom.left.base = p.hom.left.base ⁻¹' range j.hom.left.base := by
  let := hj
  -- the comparison map, from the universal property of `p`
  have hW1 : HasRankOneData (nativePulledIdealModule (pW ≫ j).hom.left
      (intrinsicReducedCentreIdealModule X.obj.left C)
      (intrinsicReducedCentreIdealInclusion X.obj.left C)) :=
    (hasRankOneData_comp_openImmersion_iff pW.hom.left j.hom.left C).mpr hpW.1
  obtain ⟨L, hL, hLuniq⟩ := hp.2 YW (pW ≫ j) hW1
  -- the open subspace over `range j`
  let V : Opens Y.obj.left :=
    ⟨p.hom.left.base ⁻¹' range j.hom.left.base,
      hj.base_open.isOpen_range.preimage p.hom.left.base.hom.continuous⟩
  let : ParacompactSpace V := paracompactSpace_preimage_range p hprop j hj
  let YV := openSubspace Y V
  let ι := openSubspaceInclusion Y V
  have hιr : range ι.hom.left.base = p.hom.left.base ⁻¹' range j.hom.left.base :=
    range_openSubspaceInclusion Y V
  have hι1 : HasRankOneData (nativePulledIdealModule (ι ≫ p).hom.left
      (intrinsicReducedCentreIdealModule X.obj.left C)
      (intrinsicReducedCentreIdealInclusion X.obj.left C)) :=
    hasRankOneData_comp_openImmersion ι.hom.left p.hom.left _ _ hp.1
  -- the restricted projection `YV ⟶ W`
  have hr : range (ι ≫ p).hom.left.base ⊆ range j.hom.left.base := by
    rintro _ ⟨v, rfl⟩
    have hv : ι.hom.left.base v ∈ range ι.hom.left.base := ⟨v, rfl⟩
    rw [hιr] at hv
    exact hv
  let qL := LocallyRingedSpace.IsOpenImmersion.lift j.hom.left (ι ≫ p).hom.left hr
  have hqL : qL ≫ j.hom.left = (ι ≫ p).hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac j.hom.left (ι ≫ p).hom.left hr
  have hqw : qL ≫ W.obj.hom = YV.obj.hom := by
    rw [← Over.w j.hom, ← Category.assoc, hqL]
    exact Over.w (ι ≫ p).hom
  let q : YV ⟶ W := ObjectProperty.homMk (Over.homMk qL hqw)
  have hqj : q ≫ j = ι ≫ p := hom_ext_of_mono hqL
  have hq1 : HasRankOneData (nativePulledIdealModule q.hom.left
      (intrinsicReducedCentreIdealModule W.obj.left (j.hom.left.base ⁻¹' C))
      (intrinsicReducedCentreIdealInclusion W.obj.left (j.hom.left.base ⁻¹' C))) := by
    apply (hasRankOneData_comp_openImmersion_iff q.hom.left j.hom.left C).mp
    change HasRankOneData (nativePulledIdealModule (q ≫ j).hom.left _ _)
    rw [hqj]
    exact hι1
  obtain ⟨M, hM, -⟩ := hpW.2 YV q hq1
  -- `L` factors through the open subspace
  have hr' : range L.hom.left.base ⊆ range ι.hom.left.base := by
    rw [hιr]
    rintro _ ⟨y, rfl⟩
    refine ⟨pW.hom.left.base y, ?_⟩
    change (pW ≫ j).hom.left.base y = (L ≫ p).hom.left.base y
    rw [hL]
  let L'L := LocallyRingedSpace.IsOpenImmersion.lift ι.hom.left L.hom.left hr'
  have hL'L : L'L ≫ ι.hom.left = L.hom.left :=
    LocallyRingedSpace.IsOpenImmersion.lift_fac ι.hom.left L.hom.left hr'
  have hL'w : L'L ≫ YV.obj.hom = YW.obj.hom := by
    rw [← Over.w ι.hom, ← Category.assoc, hL'L]
    exact Over.w L.hom
  let L' : YW ⟶ YV := ObjectProperty.homMk (Over.homMk L'L hL'w)
  have hL'ι : L' ≫ ι = L := hom_ext_of_mono hL'L
  -- `L'` and `M` are mutually inverse
  have hj_cancel : ∀ {T : SourceReducedComplexSpace} {f g : T ⟶ W}, f ≫ j = g ≫ j → f = g := by
    intro T f g h
    apply hom_ext_of_mono
    exact (cancel_mono j.hom.left).mp (congrArg (fun F => F.hom.left) h)
  have hι_cancel : ∀ {T : SourceReducedComplexSpace} {f g : T ⟶ YV}, f ≫ ι = g ≫ ι → f = g := by
    intro T f g h
    apply hom_ext_of_mono
    exact (cancel_mono ι.hom.left).mp (congrArg (fun F => F.hom.left) h)
  have h₁ : L' ≫ M = 𝟙 YW := by
    obtain ⟨N, -, hN⟩ := hpW.2 YW pW hpW.1
    have hq : L' ≫ q = pW := hj_cancel (by rw [Category.assoc, hqj, ← Category.assoc, hL'ι, hL])
    have ha := hN (L' ≫ M) (by
      show (L' ≫ M) ≫ pW = pW
      rw [Category.assoc, hM, hq])
    have hb := hN (𝟙 YW) (Category.id_comp pW)
    exact ha.trans hb.symm
  have h₂ : M ≫ L' = 𝟙 YV := by
    obtain ⟨N, -, hN⟩ := hp.2 YV (ι ≫ p) hι1
    have ha := hN ((M ≫ L') ≫ ι) (by
      show ((M ≫ L') ≫ ι) ≫ p = ι ≫ p
      calc ((M ≫ L') ≫ ι) ≫ p = M ≫ ((L' ≫ ι) ≫ p) := by simp only [Category.assoc]
        _ = M ≫ (pW ≫ j) := by rw [hL'ι, hL]
        _ = q ≫ j := by rw [← Category.assoc, hM]
        _ = ι ≫ p := hqj)
    have hb := hN ι rfl
    exact hι_cancel ((ha.trans hb.symm).trans (Category.id_comp ι).symm)
  let e : YW ≅ YV := ⟨L', M, h₁, h₂⟩
  have heL : e.hom.hom.left = L'L := rfl
  have hiso : IsIso L'L := by
    rw [← heL]
    exact (Functor.mapIso (ObjectProperty.ι _ ⋙ Over.forget _) e).isIso_hom
  refine ⟨L, ⟨hL, fun L₁ h₁ => hLuniq L₁ h₁⟩, ?_, ?_⟩
  · rw [← hL'L]
    infer_instance
  · rw [← hιr, ← hL'L]
    have hsurj : Function.Surjective L'L.base := by
      intro v
      refine ⟨M.hom.left.base v, ?_⟩
      have h := congrArg (fun F => F.hom.left.base v) h₂
      exact h
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨L'L.base w, rfl⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨w, rfl⟩ := hsurj v
      exact ⟨w, rfl⟩

/-- **Locality of a smooth-centre blowup**: the blowup of `X` along a smooth centre `i`, restricted
over an open immersion `j : W ⟶ X`, is every ideal blowup of the trace of the centre on `W`. -/
theorem exists_openImmersion_of_isSmoothCentreBlowup {X Y S W YW : SourceReducedComplexSpace}
    {p : Y ⟶ X} {i : S ⟶ X} (hp : IsSmoothCentreBlowup p i) {j : W ⟶ X}
    (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left) {pW : YW ⟶ W}
    (hpW : IsIdealBlowup pW
      (intrinsicReducedCentreIdealModule W.obj.left (j.hom.left.base ⁻¹' range i.hom.left.base))
      (intrinsicReducedCentreIdealInclusion W.obj.left
        (j.hom.left.base ⁻¹' range i.hom.left.base))) :
    ∃ L : YW ⟶ Y, (L ≫ p = pW ≫ j ∧ ∀ L₁ : YW ⟶ Y, L₁ ≫ p = pW ≫ j → L₁ = L) ∧
      LocallyRingedSpace.IsOpenImmersion L.hom.left ∧
      range L.hom.left.base = p.hom.left.base ⁻¹' range j.hom.left.base :=
  exists_openImmersion_of_isIdealBlowup hj hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.1 hpW

/-- Locality between two smooth-centre blowups, the local centre being the trace of the global
one. -/
theorem exists_openImmersion_of_isSmoothCentreBlowup_of_trace
    {X Y S W YW SW : SourceReducedComplexSpace} {p : Y ⟶ X} {i : S ⟶ X}
    (hp : IsSmoothCentreBlowup p i) {j : W ⟶ X} (hj : LocallyRingedSpace.IsOpenImmersion j.hom.left)
    {pW : YW ⟶ W} {iW : SW ⟶ W} (hpW : IsSmoothCentreBlowup pW iW)
    (htrace : range iW.hom.left.base = j.hom.left.base ⁻¹' range i.hom.left.base) :
    ∃ L : YW ⟶ Y, (L ≫ p = pW ≫ j ∧ ∀ L₁ : YW ⟶ Y, L₁ ≫ p = pW ≫ j → L₁ = L) ∧
      LocallyRingedSpace.IsOpenImmersion L.hom.left ∧
      range L.hom.left.base = p.hom.left.base ⁻¹' range j.hom.left.base := by
  have h := hpW.2.2.2.2.2.1
  rw [htrace] at h
  exact exists_openImmersion_of_isSmoothCentreBlowup hp hj h

end Locality

end

end Hironaka.Analytic.Unibranch.HironakaG11BlowupLocality
