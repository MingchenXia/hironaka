import Hironaka.Resolution.HironakaG10PNIdealNoetherModel
import Hironaka.Resolution.HironakaActualAnalyticSubspaceLocalFunctions
import Hironaka.Resolution.HironakaG10ChowFibreAlgebra

/-! Coherence of the ideal of a point and of the fibre ideals `𝔪_z 𝒪_Y` (lane G10P, run 0080 r4).
Blueprint: `hironaka-g10-pn-point-ideal.tex`.

* Germ extension: a section whose germ at `p` lies in a locally finitely generated ideal family has
  its germs in the family at every point near `p` (`IsLocallyFinitelyGenerated.exists_nhds_mem`).
* Local finite generation ascends along open immersions
  (`isLocallyFinitelyGenerated_of_openImmersion`).
* The point family `pointFamily X z` (`𝔪_z` at `z`, the unit ideal elsewhere) is locally finitely
  generated as soon as the stalk at `z` is noetherian, `{z}` is closed and finitely many sections near
  `z` vanish at `z` and have no other common zero (`isLocallyFinitelyGenerated_pointFamily_of`); on an
  embedded analytic model the shifted coordinates do this (`isLocallyFinitelyGenerated_pointFamily_model`),
  hence on every T1 space with analytic model charts (`isLocallyFinitelyGenerated_pointFamily_of_charts`).
* The fibre ideals `𝔪_{f y} 𝒪_{Y,y}` of a morphism are the pulled point family
  (`pullFamily_pointFamily_self`), so the fibre ideal family of a point of the target is coherent
  (`isLocallyFinitelyGenerated_fibreFamily`). -/

set_option autoImplicit false
open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry IsLocalRing
open scoped Manifold ContDiff

namespace Hironaka.HironakaG10PNPointIdeal

open HironakaG10PNIdealFamily

noncomputable section

universe u

section Germs

variable {X : LocallyRingedSpace.{u}}

theorem mem_finsetInf_opens {ι : Type*} [DecidableEq ι] (B : ι → Opens X) (s : Finset ι)
    (x : X) : x ∈ s.inf B ↔ ∀ i ∈ s, x ∈ B i := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.inf_empty, Opens.mem_top, Finset.notMem_empty, IsEmpty.forall_iff,
      implies_true]
  | insert i s _ ih =>
    simp only [Finset.inf_insert, Opens.mem_inf, ih, Finset.mem_insert, forall_eq_or_imp]

/-- Finitely many germs at `p` are the germs of sections over ONE open. -/
theorem exists_common_sections {r : ℕ} (p : X) (g : Fin r → X.presheaf.stalk p) :
    ∃ (V : Opens X) (hp : p ∈ V) (a : Fin r → X.presheaf.obj (op V)),
      ∀ i, X.presheaf.germ V p hp (a i) = g i := by
  classical
  choose V hV a ha using fun i => TopCat.Presheaf.exists_germ_eq X.presheaf (g i)
  have hp : p ∈ Finset.univ.inf V := (mem_finsetInf_opens V _ p).mpr fun i _ => hV i
  refine ⟨Finset.univ.inf V, hp,
    fun i => X.presheaf.map (homOfLE (Finset.inf_le (Finset.mem_univ i))).op (a i), fun i => ?_⟩
  rw [TopCat.Presheaf.germ_res_apply]
  exact ha i

/-- **Germ extension for a finite span.**  If the germ of `t` at `p` lies in the ideal spanned by
the germs of finitely many sections `a i`, the same holds at every point of an open `O ∋ p`. -/
theorem exists_nhds_germ_mem_span {V V' : Opens X} {r : ℕ} (a : Fin r → X.presheaf.obj (op V))
    (t : X.presheaf.obj (op V')) (p : X) (hp : p ∈ V) (hp' : p ∈ V')
    (h : X.presheaf.germ V' p hp' t ∈
      Ideal.span (range fun i => X.presheaf.germ V p hp (a i))) :
    ∃ (O : Opens X) (_ : p ∈ O) (hOV : O ≤ V) (hOV' : O ≤ V'),
      ∀ (q : X) (hq : q ∈ O), X.presheaf.germ V' q (hOV' hq) t ∈
        Ideal.span (range fun i => X.presheaf.germ V q (hOV hq) (a i)) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp h
  obtain ⟨D, hpD, d, hd⟩ := exists_common_sections p c
  let O₀ : Opens X := V ⊓ V' ⊓ D
  have hpO₀ : p ∈ O₀ := ⟨⟨hp, hp'⟩, hpD⟩
  let i₁ : O₀ ⟶ V := homOfLE (inf_le_left.trans inf_le_left)
  let i₂ : O₀ ⟶ V' := homOfLE (inf_le_left.trans inf_le_right)
  let i₃ : O₀ ⟶ D := homOfLE inf_le_right
  let S : X.presheaf.obj (op O₀) :=
    ∑ i, X.presheaf.map i₃.op (d i) * X.presheaf.map i₁.op (a i)
  have hS : ∀ (q : X) (hq : q ∈ O₀), X.presheaf.germ O₀ q hq S =
      ∑ i, X.presheaf.germ D q (i₃.le hq) (d i) * X.presheaf.germ V q (i₁.le hq) (a i) := by
    intro q hq
    simp only [S, map_sum, map_mul, TopCat.Presheaf.germ_res_apply]
  have hgerm : X.presheaf.germ O₀ p hpO₀ (X.presheaf.map i₂.op t) =
      X.presheaf.germ O₀ p hpO₀ S := by
    rw [hS, TopCat.Presheaf.germ_res_apply, ← hc]
    exact Finset.sum_congr rfl fun i _ => by rw [hd i]
  obtain ⟨O, hpO, j₁, j₂, hO⟩ := TopCat.Presheaf.germ_eq X.presheaf p hpO₀ hpO₀ _ _ hgerm
  refine ⟨O, hpO, j₁.le.trans i₁.le, j₁.le.trans i₂.le, fun q hq => ?_⟩
  have e1 : X.presheaf.germ V' q (j₁.le.trans i₂.le hq) t =
      X.presheaf.germ O q hq (X.presheaf.map j₁.op (X.presheaf.map i₂.op t)) := by
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply]
  have e2 : X.presheaf.germ O q hq (X.presheaf.map j₂.op S) = X.presheaf.germ O₀ q (j₂.le hq) S :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  rw [e1, hO, e2, hS]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- **Germ extension.**  A section whose germ at `p` lies in a locally finitely generated ideal
family has its germ in the family at every point of an open `O ∋ p`. -/
theorem exists_nhds_mem_of_isLocallyFinitelyGenerated {J : ∀ x : X, Ideal (X.presheaf.stalk x)}
    (hJ : IsLocallyFinitelyGenerated X J) {V : Opens X} (t : X.presheaf.obj (op V)) (p : X)
    (hp : p ∈ V) (h : X.presheaf.germ V p hp t ∈ J p) :
    ∃ (O : Opens X) (_ : p ∈ O) (hOV : O ≤ V),
      ∀ (q : X) (hq : q ∈ O), X.presheaf.germ V q (hOV hq) t ∈ J q := by
  obtain ⟨W, hpW, r, s, hs⟩ := hJ p
  rw [hs p hpW] at h
  obtain ⟨O, hpO, hOW, hOV, hO⟩ := exists_nhds_germ_mem_span s t p hpW hp h
  refine ⟨O, hpO, hOV, fun q hq => ?_⟩
  rw [hs q (hOW hq)]
  exact hO q hq

/-- A locally finitely generated family is the unit ideal near a point where it is the unit
ideal. -/
theorem exists_nhds_eq_top_of_isLocallyFinitelyGenerated {J : ∀ x : X, Ideal (X.presheaf.stalk x)}
    (hJ : IsLocallyFinitelyGenerated X J) (p : X) (h : J p = ⊤) :
    ∃ (O : Opens X) (_ : p ∈ O), ∀ q : X, q ∈ O → J q = ⊤ := by
  have h1 : X.presheaf.germ ⊤ p trivial 1 ∈ J p := by rw [h]; exact Submodule.mem_top
  obtain ⟨O, hpO, _hOV, hO⟩ := exists_nhds_mem_of_isLocallyFinitelyGenerated hJ (V := ⊤) 1 p trivial h1
  refine ⟨O, hpO, fun q hq => ?_⟩
  have := hO q hq
  rw [map_one] at this
  exact (Ideal.eq_top_iff_one _).mpr this

end Germs

section OpenImmersion

variable {X Y : LocallyRingedSpace.{u}}

/-- The image of a bijective ring map between local rings carries the maximal ideal onto the maximal
ideal. -/
theorem map_maximalIdeal_of_bijective {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (φ : R →+* S) (hφ : Function.Bijective φ) :
    Ideal.map φ (maximalIdeal R) = maximalIdeal S := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro r hr
    change φ r ∈ maximalIdeal S
    rw [mem_maximalIdeal, mem_nonunits_iff] at hr ⊢
    intro hu
    apply hr
    have e := RingEquiv.ofBijective φ hφ
    have := hu.map (RingEquiv.ofBijective φ hφ).symm
    rwa [show (RingEquiv.ofBijective φ hφ).symm (φ r) = r from
      (RingEquiv.ofBijective φ hφ).symm_apply_apply r] at this
  · intro s hs
    obtain ⟨r, rfl⟩ := hφ.2 s
    apply Ideal.mem_map_of_mem
    rw [mem_maximalIdeal, mem_nonunits_iff] at hs ⊢
    exact fun hu => hs (hu.map φ)

/-- **Local finite generation ascends along an open immersion**: if the pulled family is locally
finitely generated at `y`, the family is so at `f y` (push the generating sections with the inverse
of the open immersion). -/
theorem isLocallyFinitelyGenerated_of_openImmersion (f : Y ⟶ X)
    [H : LocallyRingedSpace.IsOpenImmersion f] {J : ∀ x : X, Ideal (X.presheaf.stalk x)}
    (hJ : IsLocallyFinitelyGenerated Y (pullFamily f J)) (y : Y) :
    ∃ (W : Opens X) (_ : f.base y ∈ W) (r : ℕ) (s : Fin r → X.presheaf.obj (op W)),
      ∀ (x : X) (hx : x ∈ W), J x = Ideal.span (range fun i => X.presheaf.germ W x hx (s i)) := by
  obtain ⟨W, hyW, r, s, hs⟩ := hJ y
  have key : ∀ (y' : Y) (hy' : y' ∈ W)
      (hx : f.base y' ∈ (LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj W),
      J (f.base y') = Ideal.span (range fun i =>
        X.presheaf.germ ((LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj W) (f.base y') hx
          (LocallyRingedSpace.IsOpenImmersion.invApp f W (s i))) := by
    intro y' hy' hx
    have hbij : Function.Bijective (f.stalkMap y').hom :=
      (asIso (f.stalkMap y')).commRingCatIsoToRingEquiv.bijective
    have hle : (Opens.map f.base).obj ((LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj W)
        ≤ W := by
      rintro z ⟨z', hz', e⟩
      exact H.base_open.injective e ▸ hz'
    have hgerm : ∀ i, Y.presheaf.germ W y' hy' (s i) = (f.stalkMap y').hom
        (X.presheaf.germ ((LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj W) (f.base y')
          hx (LocallyRingedSpace.IsOpenImmersion.invApp f W (s i))) := by
      intro i
      calc Y.presheaf.germ W y' hy' (s i)
          = Y.presheaf.germ ((Opens.map f.base).obj
              ((LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj W)) y' hx
              (Y.presheaf.map (homOfLE hle).op (s i)) :=
            (TopCat.Presheaf.germ_res_apply Y.presheaf (homOfLE hle) y' hx (s i)).symm
        _ = Y.presheaf.germ ((Opens.map f.base).obj
              ((LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj W)) y' hx
              (f.c.app (op ((LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj W))
                (LocallyRingedSpace.IsOpenImmersion.invApp f W (s i))) :=
            congrArg _ (LocallyRingedSpace.IsOpenImmersion.invApp_app_apply f W (s i)).symm
        _ = _ := (LocallyRingedSpace.stalkMap_germ_apply f _ y' hx _).symm
    have h1 := hs y' hy'
    simp only [hgerm] at h1
    rw [Set.range_comp' (f.stalkMap y').hom, ← Ideal.map_span] at h1
    rw [← Ideal.comap_map_of_bijective _ hbij (I := J (f.base y'))]
    change Ideal.comap (f.stalkMap y').hom (pullFamily f J y') = _
    rw [h1, Ideal.comap_map_of_bijective _ hbij]
  refine ⟨(LocallyRingedSpace.IsOpenImmersion.opensFunctor f).obj W, ⟨y, hyW, rfl⟩, r,
    fun i => LocallyRingedSpace.IsOpenImmersion.invApp f W (s i), ?_⟩
  rintro x ⟨y', hy', rfl⟩
  exact key y' hy' _

end OpenImmersion

section Point

variable (X : LocallyRingedSpace.{u})

/-- The ideal family of a point `z`: the maximal ideal `𝔪_z` at `z`, the unit ideal elsewhere. -/
def pointFamily (z : X) (x : X) : Ideal (X.presheaf.stalk x) := by
  classical
  exact if x = z then maximalIdeal (X.presheaf.stalk x) else ⊤

variable {X}

theorem pointFamily_self (z : X) : pointFamily X z z = maximalIdeal (X.presheaf.stalk z) := by
  simp [pointFamily]

theorem pointFamily_of_ne {z x : X} (h : x ≠ z) : pointFamily X z x = ⊤ := by
  simp [pointFamily, h]

/-- **A criterion for the coherence of the ideal of a point.**  If `{z}` is closed, the stalk at `z`
is noetherian and finitely many sections near `z` vanish at `z` but have no other common zero, then
the point family is locally finitely generated. -/
theorem isLocallyFinitelyGenerated_pointFamily_of {z : X} (hz : IsClosed ({z} : Set X))
    (hN : IsNoetherianRing (X.presheaf.stalk z)) {W : Opens X} (hzW : z ∈ W) {k : ℕ}
    (u : Fin k → X.presheaf.obj (op W))
    (hu : ∀ j, X.presheaf.germ W z hzW (u j) ∈ maximalIdeal (X.presheaf.stalk z))
    (hunit : ∀ (y : X) (hy : y ∈ W), y ≠ z → ∃ j, IsUnit (X.presheaf.germ W y hy (u j))) :
    IsLocallyFinitelyGenerated X (pointFamily X z) := by
  classical
  intro x
  by_cases hx : x = z
  · subst hx
    obtain ⟨r, g, hg⟩ := (Submodule.fg_iff_exists_fin_generating_family).mp
      (IsNoetherian.noetherian (maximalIdeal (X.presheaf.stalk x)))
    obtain ⟨V, hxV, a, ha⟩ := exists_common_sections x g
    have hga : (range fun i => X.presheaf.germ V x hxV (a i)) = range g := by
      simp only [ha]
    have hmem : ∀ j, X.presheaf.germ W x hzW (u j) ∈
        Ideal.span (range fun i => X.presheaf.germ V x hxV (a i)) := by
      intro j
      rw [hga]
      have : Ideal.span (range g) = maximalIdeal (X.presheaf.stalk x) := hg
      rw [this]
      exact hu j
    choose O hxO hOV hOW hO using fun j => exists_nhds_germ_mem_span a (u j) x hxV hzW (hmem j)
    let W' : Opens X := V ⊓ W ⊓ Finset.univ.inf O
    have hxW' : x ∈ W' := ⟨⟨hxV, hzW⟩, (mem_finsetInf_opens O _ x).mpr fun j _ => hxO j⟩
    let ι : W' ⟶ V := homOfLE (inf_le_left.trans inf_le_left)
    refine ⟨W', hxW', r, fun i => X.presheaf.map ι.op (a i), fun y hy => ?_⟩
    have hgy : (range fun i => X.presheaf.germ W' y hy (X.presheaf.map ι.op (a i))) =
        range fun i => X.presheaf.germ V y (ι.le hy) (a i) := by
      simp only [TopCat.Presheaf.germ_res_apply]
    rw [hgy]
    by_cases hyx : y = x
    · subst hyx
      rw [pointFamily_self, hga]
      exact hg.symm
    · rw [pointFamily_of_ne hyx]
      obtain ⟨j, hj⟩ := hunit y hy.1.2 hyx
      have hyO : y ∈ O j := (mem_finsetInf_opens O _ y).mp hy.2 j (Finset.mem_univ j)
      symm
      exact Ideal.eq_top_of_isUnit_mem _ (hO j y hyO) hj
  · refine ⟨⟨{z}ᶜ, hz.isOpen_compl⟩, hx, 1, fun _ => 1, fun y hy => ?_⟩
    rw [pointFamily_of_ne hy]
    symm
    rw [Ideal.eq_top_iff_one]
    exact Ideal.subset_span ⟨0, map_one _⟩

/-- The pulled point family along an open immersion is the point family of the preimage point. -/
theorem pullFamily_pointFamily_of_injective {Y : LocallyRingedSpace.{u}} (f : Y ⟶ X)
    (hinj : Function.Injective f.base) (hbij : ∀ y, Function.Bijective (f.stalkMap y).hom)
    (c : Y) (y : Y) : pullFamily f (pointFamily X (f.base c)) y = pointFamily Y c y := by
  by_cases h : y = c
  · subst h
    rw [pullFamily, pointFamily_self, pointFamily_self]
    exact map_maximalIdeal_of_bijective _ (hbij y)
  · rw [pullFamily, pointFamily_of_ne (fun e => h (hinj e)), pointFamily_of_ne h, Ideal.map_top]

/-- The fibre ideal `𝔪_{f y} 𝒪_{Y,y}` is the pulled point family at `y`. -/
theorem pullFamily_pointFamily_self {Y : LocallyRingedSpace.{u}} (f : Y ⟶ X) (y : Y) :
    pullFamily f (pointFamily X (f.base y)) y =
      HironakaG10ChowFibreAlgebra.lrsFibreIdeal f y := by
  rw [pullFamily, pointFamily_self]
  rfl

/-- Off the fibre the pulled point family is the unit ideal. -/
theorem pullFamily_pointFamily_of_ne {Y : LocallyRingedSpace.{u}} (f : Y ⟶ X) {z : X} {y : Y}
    (h : f.base y ≠ z) : pullFamily f (pointFamily X z) y = ⊤ := by
  rw [pullFamily, pointFamily_of_ne h, Ideal.map_top]

end Point

section Model

open Hironaka.HolomorphicIdealSheaves HironakaActualAnalyticSubspace
  HironakaSmoothCentreRealDomainActualSheafStalk HironakaActualAnalyticSubspaceResidue
  HironakaActualAnalyticSubspaceLocalFunctions HironakaReducedComplexAnalyticSpaces
  HironakaG10PNIdealNoetherModel

variable {n : ℕ}

/-- The shifted coordinate `z ↦ z i - a` as a holomorphic section on an original open. -/
def shiftedCoordinateSection (V : Opens (ComplexModel n)) (i : Fin n) (a : ℂ) :
    actualComplexSection (n := n) (⊤ : Opens V) := by
  have h₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ (fun z : ComplexModel n => z i - a) :=
    ((EuclideanSpace.proj (𝕜 := ℂ) i).contDiff.sub contDiff_const).contMDiff
  have h₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ℂ) ∞ (fun z : V => z.val i - a) :=
    h₀.comp contMDiff_subtype_val
  change C^∞⟮𝓘(ℂ, ComplexModel n), (⊤ : Opens V); 𝓘(ℂ, ℂ), ℂ⟯
  exact ⟨fun z => z.val.val i - a, h₁.comp contMDiff_subtype_val⟩

theorem shiftedCoordinateSection_apply (V : Opens (ComplexModel n)) (i : Fin n) (a : ℂ)
    (z : (⊤ : Opens V)) : shiftedCoordinateSection V i a z = z.val.val i - a := rfl

/-- The stalks of an embedded analytic model are noetherian. -/
theorem isNoetherianRing_modelStalk (U : Opens (ComplexModel n)) (C : Set U) (c : C) :
    IsNoetherianRing ((actualSubspaceLocallyRingedSpace (n := n) C).presheaf.stalk c) := by
  have : IsNoetherianRing (HolGerm (ComplexModel n)) := isNoetherianRing_holGerm_euclidean n
  exact isNoetherianRing_of_ringEquiv _ (actualSubspaceStalkChartEquiv (n := n) C c).symm

/-- **The ideal of a point of an embedded analytic model is coherent** (the shifted coordinates
`z_i - c_i` vanish only at `c`). -/
theorem isLocallyFinitelyGenerated_pointFamily_model (U : Opens (ComplexModel n)) (C : Set U)
    (c : C) : IsLocallyFinitelyGenerated (actualSubspaceLocallyRingedSpace (n := n) C)
      (pointFamily (actualSubspaceLocallyRingedSpace (n := n) C) c) := by
  let Y := actualSubspaceLocallyRingedSpace (n := n) C
  let ι := actualSubspaceInclusion (n := n) C
  let W : Opens Y := (Opens.map ι.base).obj ⊤
  let u : Fin n → Y.presheaf.obj (op W) := fun i =>
    ι.c.app (op ⊤) (shiftedCoordinateSection U i (c.val.val i))
  have hval : ∀ (y : Y) (hy : y ∈ W) (i : Fin n),
      actualSubspaceStalkEval (n := n) C y (Y.presheaf.germ W y hy (u i)) =
        y.val.val i - c.val.val i := by
    intro y hy i
    have h := actualSubspaceStalkEval_inclusion_germ (n := n) C ⊤
      (shiftedCoordinateSection U i (c.val.val i)) y trivial
    have h2 : Y.presheaf.germ W y hy (u i) = ι.stalkMap y
        ((actualComplexStructureSheaf (n := n) U).presheaf.germ ⊤ y.val trivial
          (shiftedCoordinateSection U i (c.val.val i))) :=
      (LocallyRingedSpace.stalkMap_germ_apply ι ⊤ y hy _).symm
    rw [h2]
    exact h
  have hmax : ∀ (y : Y) (g : Y.presheaf.stalk y),
      g ∈ maximalIdeal (Y.presheaf.stalk y) ↔ actualSubspaceStalkEval (n := n) C y g = 0 := by
    intro y g
    have := actualSubspaceStalk_isLocalRing (n := n) C y
    change g ∈ maximalIdeal ((actualSubspaceSheaf (n := n) C).presheaf.stalk y) ↔ _
    rw [← actualSubspaceStalkEval_ker (n := n) C y, RingHom.mem_ker]
  refine isLocallyFinitelyGenerated_pointFamily_of (show IsClosed ({c} : Set C) from isClosed_singleton)
    (isNoetherianRing_modelStalk U C c) (show c ∈ W from trivial) u (fun i => ?_) ?_
  · rw [hmax, hval, sub_self]
  · intro y hy hyc
    have hne : y.val.val ≠ c.val.val := fun e => hyc (Subtype.ext (Subtype.ext e))
    obtain ⟨i, hi⟩ : ∃ i, y.val.val i ≠ c.val.val i := by
      by_contra hall
      exact hne (PiLp.ext fun i => not_not.mp fun h => hall ⟨i, h⟩)
    refine ⟨i, ?_⟩
    by_contra hu
    have : Y.presheaf.germ W y hy (u i) ∈ maximalIdeal (Y.presheaf.stalk y) :=
      (mem_maximalIdeal _).mpr hu
    rw [hmax, hval, sub_eq_zero] at this
    exact hi this

/-- **The ideal of a point is coherent** on every T1 space with analytic model charts. -/
theorem isLocallyFinitelyGenerated_pointFamily_of_charts {X : LocallyRingedSpace.{0}}
    (hX : HasAnalyticModelCharts X) [T1Space X] (z : X) :
    IsLocallyFinitelyGenerated X (pointFamily X z) := by
  intro x
  by_cases hx : x = z
  · subst hx
    obtain ⟨n, U, C, -, i, hi, c, rfl⟩ := hX x
    have hinj : Function.Injective i.base := hi.base_open.injective
    have hbij : ∀ y, Function.Bijective (i.stalkMap y).hom := fun y =>
      (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv.bijective
    have hpull : IsLocallyFinitelyGenerated (modelOver U C).left
        (pullFamily i (pointFamily X (i.base c))) := by
      have e : pullFamily i (pointFamily X (i.base c)) = pointFamily (modelOver U C).left c :=
        funext fun y => pullFamily_pointFamily_of_injective i hinj hbij c y
      rw [e]
      exact isLocallyFinitelyGenerated_pointFamily_model U C c
    exact isLocallyFinitelyGenerated_of_openImmersion i hpull c
  · refine ⟨⟨{z}ᶜ, isClosed_singleton.isOpen_compl⟩, hx, 1, fun _ => 1, fun y hy => ?_⟩
    rw [pointFamily_of_ne hy]
    symm
    rw [Ideal.eq_top_iff_one]
    exact Ideal.subset_span ⟨0, map_one _⟩

/-- **The fibre ideal family of a point is coherent**: for `f : Y ⟶ X` with `X` a T1 space with
analytic model charts and `z : X`, the family `𝔪_z 𝒪_{Y,y}` (unit ideal off `f⁻¹(z)`) is locally
finitely generated. -/
theorem isLocallyFinitelyGenerated_fibreFamily {X Y : LocallyRingedSpace.{0}}
    (hX : HasAnalyticModelCharts X) [T1Space X] (f : Y ⟶ X) (z : X) :
    IsLocallyFinitelyGenerated Y (pullFamily f (pointFamily X z)) :=
  isLocallyFinitelyGenerated_pull f (isLocallyFinitelyGenerated_pointFamily_of_charts hX z)

end Model

end

end Hironaka.HironakaG10PNPointIdeal
