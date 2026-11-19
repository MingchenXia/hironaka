import Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
import Hironaka.Analytic.Unibranch.HironakaG10GermFlattenerSquareTransport

/-!
# Relative non-flat sets along a permissible step (lane G10RD)

Plan item G10-03-15.b (the compatibility `hSπ` consumed by the relative termination of Theorem `II_n`,
lane G10TM's `machine_exists_eq_empty_of_rounds`).  Source: H. Hironaka, *Flattening theorem in
complex-analytic geometry*, Amer. J. Math. 97 (1975), proof of Lemma 4.6.1, printed p. 545: "By the
permissibility of Π^{(1)}, Π^{(1)} maps s_1(F^{(1)}, f^{(1)}/B^{(1)}) into s_1(F, f/B)."

* `map_vanishingIdealAt_le` — germs vanishing on `A` pull back to germs vanishing on any `A' ⊆ σ⁻¹ A`;
* `strictSet_subset_preimage` — the strict transform of a closed set lies in its inverse image;
* `germFlattener_next_eq` — off the centre the whole-fibre flattener of the strict transform is the
  pull-back of the old one (isomorphic stalk square);
* `flatOverAt_next_of_flatOverAt` — off the centre, flatness over `B` at `σ x'` gives flatness over the
  strict transform of `B` at `x'`;
* `vanishingIdealAt_le_maximalIdeal`, `eventually_le_vanishingIdealAt`, **`isClosed_relNonflat`** — from the
  local input `PersistentLocalFlattener`, the relative non-flat set over a closed set is closed (the
  `hS` of the relative termination);
* **`PermStep.mapsTo_relNonflat`** — a permissible step maps `s_1(f_1/B_1)` into `s_1(f/B)` (at centre
  points by permissibility (2), elsewhere by the previous lemma).

No named input is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory Opposite AlgebraicGeometry
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10RdRelativeStep

open Hironaka HironakaSingularModuleSheafStalk HironakaG10HirIdealGerms
open Hironaka.Analytic.Unibranch.HironakaG10ChowFlattenerDecrease
  Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10GermFlattenerSquareTransport
  Hironaka.Analytic.Unibranch.HironakaG10ChowOneStepStrictTransform
  Hironaka.Analytic.Unibranch.HironakaG10ChowNativeIsoCriterion
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningReduction
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-- **Germs vanishing on `A` pull back to germs vanishing on `A' ⊆ σ⁻¹ A`.** -/
theorem map_vanishingIdealAt_le {X X' : LocallyRingedSpace.{0}} (σ : X' ⟶ X) (A : Set X)
    (A' : Set X') (hA : A' ⊆ σ.base ⁻¹' A) (x' : X') :
    Ideal.map (σ.stalkMap x').hom (vanishingIdealAt X A (σ.base x')) ≤
      vanishingIdealAt X' A' x' := by
  rw [vanishingIdealAt, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨g, ⟨U, hxU, t, rfl, hvan⟩, rfl⟩
  apply Ideal.subset_span
  refine ⟨(Opens.map σ.base).obj U, hxU, σ.c.app (op U) t,
    (LocallyRingedSpace.stalkMap_germ_apply σ U x' hxU t).symm, ?_⟩
  intro z hz hzA'
  have h := hvan (σ.base z) hz (hA hzA')
  rw [← LocallyRingedSpace.stalkMap_germ_apply σ U z hz t]
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h ⊢
  exact fun hu => h ((isUnit_map_iff (σ.stalkMap z).hom _).mp hu)

/-- The strict transform of a closed set lies in its inverse image. -/
theorem strictSet_subset_preimage (s : Stage) (c : AdmissibleCentre s.f) {B : Set s.X.obj.left}
    (hB : IsClosed B) : strictSet s c B ⊆ (stepσ s c).hom.left.base ⁻¹' B :=
  closure_minimal (preimage_mono sdiff_subset)
    (hB.preimage (stepσ s c).hom.left.base.hom.continuous)

/-- **Off the centre, the whole-fibre flattener of the strict transform is the pull-back of the old
one** (isomorphic stalk square). -/
theorem germFlattener_next_eq (s : Stage) (c : AdmissibleCentre s.f)
    (x' : (nextWith s c).X.obj.left)
    (hx : (stepσ s c).hom.left.base x' ∉ nonunitLocus c.B c.b) :
    germFlattener (nextWith s c).f x' =
      Ideal.map ((stepσ s c).hom.left.stalkMap x').hom
        (germFlattener s.f ((stepσ s c).hom.left.base x')) := by
  let _ := c.finiteType
  have hxE : x' ∉ stepExcep c.B c.b c.dense := hx
  have hσ : IsIso ((stepProj c.B c.b c.dense).hom.left.stalkMap x') :=
    isIso_stalkMap_of_isIsoOver (stepProj_isIsoOver c.B c.b c.dense) x' hx
  have hq : ∀ y' : (strictSource c.B c.b s.f).obj.left,
      (strictP c.B c.b c.dense s.f).hom.left.base y' = x' →
        IsIso ((strictQ c.B c.b s.f).hom.left.stalkMap y') := by
    intro y' hy'
    apply isIso_stalkMap_of_isOpenImmersionOn (strict_openImmersionOn c.B c.b c.dense s.f) y'
    change (strictP c.B c.b c.dense s.f).hom.left.base y' ∉ stepExcep c.B c.b c.dense
    simpa only [hy'] using hxE
  have hcover : ∀ y : s.Y.obj.left,
      s.f.hom.left.base y = (stepProj c.B c.b c.dense).hom.left.base x' →
        ∃ y' : (strictSource c.B c.b s.f).obj.left,
          (strictP c.B c.b c.dense s.f).hom.left.base y' = x' ∧
            (strictQ c.B c.b s.f).hom.left.base y' = y :=
    fun y hy => strict_covers c.B c.b c.dense s.f y x' hxE hy
  have hG := isGermFlattenerAt_of_isomorphic_square s.f (stepProj c.B c.b c.dense)
    (strictP c.B c.b c.dense s.f) (strictQ c.B c.b s.f) (strictP_comp c.B c.b c.dense s.f) x'
    hσ hq hcover _ (isGermFlattenerAt_germFlattener s.f _)
  exact (eq_germFlattener _ x' _ hG).symm

/-- **Off the centre, relative flatness passes to the strict transform.** -/
theorem flatOverAt_next_of_flatOverAt (s : Stage) (c : AdmissibleCentre s.f)
    {B : Set s.X.obj.left} (hB : IsClosed B) (x' : (nextWith s c).X.obj.left)
    (hx : (stepσ s c).hom.left.base x' ∉ nonunitLocus c.B c.b)
    (hflat : FlatOverAt s.f ((stepσ s c).hom.left.base x')
      (vanishingIdealAt s.X.obj.left B ((stepσ s c).hom.left.base x'))) :
    FlatOverAt (nextWith s c).f x' (vanishingIdealAt _ (strictSet s c B) x') := by
  refine (isGermFlattenerAt_germFlattener (nextWith s c).f x' _).mpr ?_
  rw [germFlattener_next_eq s c x' hx]
  refine (Ideal.map_mono ((isGermFlattenerAt_germFlattener s.f _ _).mp hflat)).trans ?_
  exact map_vanishingIdealAt_le (stepσ s c).hom.left B (strictSet s c B)
    (strictSet_subset_preimage s c hB) x'

/-- **A permissible step maps `s_1(f_1/B_1)` into `s_1(f/B)`** (Hironaka p. 545). -/
theorem PermStep.mapsTo_relNonflat {s : Stage} {q : ℕ} {R : FDatum s q} (st : PermStep R) :
    MapsTo (stepσ s st.c).hom.left.base (relNonflat (nextWith s st.c).f st.next.B)
      (relNonflat s.f R.B) := by
  intro x' hx'
  obtain ⟨hxB, hnf⟩ := hx'
  rw [st.next_B] at hxB hnf
  by_cases hD : (stepσ s st.c).hom.left.base x' ∈ nonunitLocus st.c.B st.c.b
  · exact st.sub hD
  · exact ⟨strictSet_subset_preimage s st.c R.closed hxB,
      fun hflat => hnf (flatOverAt_next_of_flatOverAt s st.c R.closed x' hD hflat)⟩

/-! ### Closedness of relative non-flat sets -/

theorem vanishingIdealAt_le_maximalIdeal {X : LocallyRingedSpace.{0}} (A : Set X) {y : X}
    (hy : y ∈ A) : vanishingIdealAt X A y ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
  refine Ideal.span_le.mpr ?_
  rintro _ ⟨U, hyU, t, rfl, hv⟩
  exact hv y hyU hy

/-- **Containment in a vanishing ideal spreads** from a point to a neighbourhood, for a locally finitely
generated family. -/
theorem eventually_le_vanishingIdealAt {X : LocallyRingedSpace.{0}} {V : Set X}
    {H : ∀ x : X, Ideal (X.presheaf.stalk x)} (hH : IsLocallyFinitelyGeneratedOn X V H)
    (hV : IsOpen V) (B : Set X) {x : X} (hx : x ∈ V) (hle : H x ≤ vanishingIdealAt X B x) :
    ∀ᶠ y in 𝓝 x, H y ≤ vanishingIdealAt X B y := by
  obtain ⟨W, hxW, r, s, hs⟩ := hH x hx
  have hgen : ∀ i, ∀ᶠ y in 𝓝 x, ∀ hy : y ∈ W,
      X.presheaf.germ W y hy (s i) ∈ vanishingIdealAt X B y := by
    intro i
    have hmem : X.presheaf.germ W x hxW (s i) ∈ vanishingIdealAt X B x :=
      hle (by rw [hs x hxW hx]; exact Ideal.subset_span ⟨i, rfl⟩)
    obtain ⟨n, c, g, hcg⟩ := Submodule.mem_span_set'.mp hmem
    choose U hxU t ht hvan using fun k => (g k).2
    let W' : Opens X := ⨅ k, U k
    have hxW' : x ∈ W' := by
      show x ∈ ((⨅ k, U k : Opens X) : Set X)
      rw [Opens.coe_iInf]
      exact mem_iInter.2 hxU
    have hW'U : ∀ k, W' ≤ U k := fun k => iInf_le _ k
    let s' : Fin n → X.presheaf.obj (op W') := fun k => X.presheaf.map (homOfLE (hW'U k)).op (t k)
    have hgerm : ∀ (y : X) (hy : y ∈ W') (k : Fin n),
        X.presheaf.germ W' y hy (s' k) = X.presheaf.germ (U k) y (hW'U k hy) (t k) := by
      intro y hy k
      simp only [s', X.presheaf.germ_res_apply]
    have hspan : X.presheaf.germ W x hxW (s i) ∈
        Ideal.span (Set.range fun k => X.presheaf.germ W' x hxW' (s' k)) := by
      rw [← hcg]
      refine Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Ideal.subset_span ⟨k, ?_⟩)
      show X.presheaf.germ W' x hxW' (s' k) = (g k : X.presheaf.stalk x)
      rw [hgerm, ht k]
    filter_upwards [eventually_germ_mem_span hxW hxW' (s i) s' hspan, W'.isOpen.mem_nhds hxW']
      with y hy hyW' hyW
    refine (Ideal.span_le.mpr ?_) (hy hyW hyW')
    rintro _ ⟨k, rfl⟩
    show X.presheaf.germ W' y hyW' (s' k) ∈ vanishingIdealAt X B y
    rw [hgerm]
    exact Ideal.subset_span ⟨U k, hW'U k hyW', t k, rfl, hvan k⟩
  filter_upwards [eventually_all.2 hgen, W.isOpen.mem_nhds hxW, hV.mem_nhds hx] with y hy hyW hyV
  rw [hs y hyW hyV, Ideal.span_le]
  rintro _ ⟨i, rfl⟩
  exact hy i hyW

/-- **The relative non-flat set over a closed set is closed**, from the local input (Hironaka quotes
Frisch for `s_1`, p. 506; here only its closedness is used). -/
theorem isClosed_relNonflat (hP : PersistentLocalFlattener) {X Y : SourceReducedComplexSpace}
    (f : Y ⟶ X) (hf : IsProperMap f.hom.left.base) {B : Set X.obj.left} (hB : IsClosed B) :
    IsClosed (relNonflat f B) := by
  rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
  intro x hx
  by_cases hxB : x ∈ B
  · have hflat : FlatOverAt f x (vanishingIdealAt X.obj.left B x) := by
      by_contra h
      exact hx ⟨hxB, h⟩
    obtain ⟨Z, hZV, hZtop⟩ := hP X Y f hf x
    have hle : Z.H x ≤ vanishingIdealAt X.obj.left B x :=
      ((Z.flattener x hZV hZtop) _).mp hflat
    filter_upwards [eventually_le_vanishingIdealAt Z.fg Z.isOpen B hZV hle,
      Z.isOpen.mem_nhds hZV] with y hy hyV
    intro h
    obtain ⟨hyB, hnf⟩ := h
    have hne : Z.H y ≠ ⊤ := fun htop =>
      (IsLocalRing.maximalIdeal.isMaximal _).ne_top
        (top_le_iff.mp ((htop ▸ hy).trans (vanishingIdealAt_le_maximalIdeal B hyB)))
    exact hnf (((Z.flattener y hyV hne) _).mpr hy)
  · filter_upwards [hB.isOpen_compl.mem_nhds hxB] with y hy h
    exact hy h.1

end

end Hironaka.Analytic.Unibranch.HironakaG10RdRelativeStep
