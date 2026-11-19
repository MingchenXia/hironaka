import Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
import Hironaka.Analytic.Unibranch.HironakaG10MwNativeWindow
import Hironaka.Resolution.HironakaG10PNKernelSquare

/-!
# Local flatteners with a prescribed support, from support germs (G10-02-11 / G10-03-09 reduction)

Lane G10SB, run 0081.  Consumer: lane G10RD's `hT` of `HironakaG10RdSumStep.exists_sumCentre_permStep`
(Hironaka 1975 Lemma 4.4.5, printed pp. 537–538: the tracked flattener `Z_p` of an (F)-datum is carried by a
permissible blowup to a local flattener `Z_{p1}` of the strict transform with `|Z_{p1}| = |Z_p^*|`).

A local flattener is determined on its support by the family (it is the whole-fibre flattener there, Rem. 2.4.4),
so the only content of "there is a local flattener with support `T`" is local: near every point of `T` SOME local
flattener has the same support germ, and `T` is closed in the open set.  Proved here:

* `support_eventually_iff` — two local flatteners have the same support near a common support point;
* `exists_localFlattener_of_support_germs` — **assembly**: an open `V`, a relatively closed `T ⊆ V` and, at every
  point of `T`, one local flattener whose support agrees with `T` near that point, give a local flattener on `V`
  with support EXACTLY `T` (and family `germFlattener` on `T`, unit ideal off `T`);
* `exists_localFlattener_of_support_germs_persistent` — the same with the local flatteners supplied by lane
  G10MW's proved `persistentLocalFlattener` (proper `f`): it suffices that EVERY local flattener through a point
  of `T` has support germ `T` there;
* `exists_localFlattener_transport_of_support_germs` — the instance for one blowup step with Lemma 4.4.5's
  transported set: `hT` of `exists_sumCentre_permStep` reduces to (Closed) relative closedness of the
  transported set in `σ⁻¹ V` and (Germ) support germ equality at its points.

No named input.  (Closed) and (Germ) are the remaining mathematical content of Lemma 4.4.5 (see
`G10SB/G10-02-09r-lemma445-route.md`).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm

open Hironaka HironakaG10PNIdealFamily HironakaG10HirIdealGerms
  HironakaG10PNKernelSquare HironakaSingularModuleSheafStalk
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine Hironaka.Analytic.Unibranch.HironakaG10RdPermRun

noncomputable section

variable {X Y : SourceReducedComplexSpace} {f : Y ⟶ X}

/-- Off its support (inside `V`) a local flattener is the unit ideal. -/
theorem H_eq_top_of_not_mem_support (Z : LocalFlattener f) {x : X.obj.left} (hxV : x ∈ Z.V)
    (hx : x ∉ Z.support) : Z.H x = ⊤ := by
  by_contra h
  exact hx ⟨hxV, h⟩

/-- Two local flatteners have the same support near a common support point (Rem. 2.4.4). -/
theorem support_eventually_iff (Z Z₁ : LocalFlattener f) {x : X.obj.left} (hx : x ∈ Z.support)
    (hx₁ : x ∈ Z₁.support) : ∀ᶠ y in 𝓝 x, (y ∈ Z.support ↔ y ∈ Z₁.support) := by
  filter_upwards [Z.eventually_eq Z₁ hx hx₁, Z.isOpen.mem_nhds hx.1, Z₁.isOpen.mem_nhds hx₁.1]
    with y hy hyV hyV₁
  rw [LocalFlattener.mem_support, LocalFlattener.mem_support, hy]
  exact ⟨fun h => ⟨hyV₁, h.2⟩, fun h => ⟨hyV, h.2⟩⟩

/-- The family `germFlattener` on `T`, the unit ideal off `T`. -/
def supportFamily (f : Y ⟶ X) (T : Set X.obj.left) :
    ∀ x : X.obj.left, Ideal (X.obj.left.presheaf.stalk x) := by
  classical
  exact fun x => if x ∈ T then germFlattener f x else ⊤

theorem supportFamily_of_mem {T : Set X.obj.left} {x : X.obj.left} (hx : x ∈ T) :
    supportFamily f T x = germFlattener f x := by
  classical
  simp only [supportFamily, if_pos hx]

theorem supportFamily_of_not_mem {T : Set X.obj.left} {x : X.obj.left} (hx : x ∉ T) :
    supportFamily f T x = ⊤ := by
  classical
  simp only [supportFamily, if_neg hx]

/-- **Assembly.**  A relatively closed `T` in an open `V` with, at each point of `T`, a local flattener whose
support has the same germ, is the support of a local flattener on `V`. -/
theorem exists_localFlattener_of_support_germs (f : Y ⟶ X) (V T : Set X.obj.left)
    (hV : IsOpen V) (hTV : T ⊆ V) (hT : IsOpen (V \ T))
    (hloc : ∀ x ∈ T, ∃ Z₁ : LocalFlattener f, x ∈ Z₁.support ∧
      ∀ᶠ y in 𝓝 x, (y ∈ T ↔ y ∈ Z₁.support)) :
    ∃ Z' : LocalFlattener f, Z'.V = V ∧ Z'.support = T ∧ ∀ x ∈ T, Z'.H x = germFlattener f x := by
  classical
  have hfg : IsLocallyFinitelyGeneratedOn X.obj.left V (supportFamily f T) := by
    intro x hxV
    by_cases hxT : x ∈ T
    · obtain ⟨Z₁, hx₁, hev⟩ := hloc x hxT
      obtain ⟨W₁, hxW₁, r, s, hs⟩ := Z₁.fg x hx₁.1
      obtain ⟨N, hNP, hNo, hxN⟩ := eventually_nhds_iff.mp hev
      let O : Opens X.obj.left := ⟨N ∩ Z₁.V, hNo.inter Z₁.isOpen⟩
      have hAt : IsLocallyFinitelyGeneratedAt X.obj.left Z₁.H x := by
        let W : Opens X.obj.left := W₁ ⊓ ⟨Z₁.V, Z₁.isOpen⟩
        refine ⟨W, ⟨hxW₁, hx₁.1⟩, r, fun i => X.obj.left.presheaf.map (homOfLE inf_le_left).op (s i),
          fun y hy => ?_⟩
        rw [hs y hy.1 hy.2]
        congr 1
        refine congrArg Set.range (funext fun i => ?_)
        exact (TopCat.Presheaf.germ_res_apply X.obj.left.presheaf _ y hy (s i)).symm
      have hcongr := hAt.congr O ⟨hxN, hx₁.1⟩ (J' := supportFamily f T) (fun y hy => by
        by_cases hyT : y ∈ T
        · rw [supportFamily_of_mem hyT]
          exact Z₁.H_eq_germFlattener ((hNP y hy.1).mp hyT)
        · rw [supportFamily_of_not_mem hyT]
          exact H_eq_top_of_not_mem_support Z₁ hy.2 (fun h => hyT ((hNP y hy.1).mpr h)))
      obtain ⟨W, hxW, r', s', hs'⟩ := hcongr
      exact ⟨W, hxW, r', s', fun y hy _ => hs' y hy⟩
    · refine ⟨⟨V \ T, hT⟩, ⟨hxV, hxT⟩, 1, fun _ => 1, fun y hy _ => ?_⟩
      rw [supportFamily_of_not_mem hy.2, eq_comm, Ideal.eq_top_iff_one]
      exact Ideal.subset_span ⟨0, map_one _⟩
  refine ⟨LocalFlattener.mk V hV (supportFamily f T) hfg (fun x _ hne => ?_), rfl, ?_,
    fun x hx => supportFamily_of_mem hx⟩
  · by_cases hxT : x ∈ T
    · rw [supportFamily_of_mem hxT]
      exact isGermFlattenerAt_germFlattener f x
    · exact absurd (supportFamily_of_not_mem hxT) hne
  · ext x
    rw [LocalFlattener.mem_support]
    change x ∈ V ∧ supportFamily f T x ≠ ⊤ ↔ x ∈ T
    constructor
    · rintro ⟨_, hne⟩
      by_contra hxT
      exact hne (supportFamily_of_not_mem hxT)
    · intro hxT
      refine ⟨hTV hxT, ?_⟩
      rw [supportFamily_of_mem hxT]
      exact ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal _).ne_top
        (germFlattener_le_maximalIdeal f x)

/-- **Assembly from the proved local input.**  For proper `f` it suffices that every local flattener through
a point of `T` has support germ `T` at that point. -/
theorem exists_localFlattener_of_support_germs_persistent (f : Y ⟶ X)
    (hf : IsProperMap f.hom.left.base) (V T : Set X.obj.left)
    (hV : IsOpen V) (hTV : T ⊆ V) (hT : IsOpen (V \ T))
    (hgerm : ∀ x ∈ T, ∀ Z₁ : LocalFlattener f, x ∈ Z₁.support →
      ∀ᶠ y in 𝓝 x, (y ∈ T ↔ y ∈ Z₁.support)) :
    ∃ Z' : LocalFlattener f, Z'.V = V ∧ Z'.support = T ∧ ∀ x ∈ T, Z'.H x = germFlattener f x := by
  refine exists_localFlattener_of_support_germs f V T hV hTV hT fun x hx => ?_
  obtain ⟨Z₁, hx₁⟩ := Hironaka.Analytic.Unibranch.HironakaG10MwNativeWindow.persistentLocalFlattener X Y f hf x
  exact ⟨Z₁, hx₁, hgerm x hx Z₁ hx₁⟩

/-- Lemma 4.4.5's transported set of a local flattener along one step. -/
def transportedSupport (s : Stage) (c : AdmissibleCentre s.f) (Z : LocalFlattener s.f) :
    Set (nextWith s c).X.obj.left :=
  {x' | (stepσ s c).hom.left.base x' ∈ Z.support ∧
    OnStrictTransform (stepσ s c) x' (germFlattener s.f ((stepσ s c).hom.left.base x'))
      (centreIdeal c ((stepσ s c).hom.left.base x'))}

theorem transportedSupport_subset (s : Stage) (c : AdmissibleCentre s.f) (Z : LocalFlattener s.f) :
    transportedSupport s c Z ⊆ (stepσ s c).hom.left.base ⁻¹' Z.V :=
  fun _ hx => hx.1.1

/-- **`hT` of `exists_sumCentre_permStep`, reduced to two local statements.**  If the transported set is
closed in `σ⁻¹ V` (Closed) and every local flattener of the strict-transform family through one of its points
has the transported set as support germ (Germ), there is a local flattener of the next stage with support
EXACTLY the transported set (Hironaka Lemma 4.4.5 (1)). -/
theorem exists_localFlattener_transport_of_support_germs (s : Stage)
    (hf : IsProperMap s.f.hom.left.base) (c : AdmissibleCentre s.f) (Z : LocalFlattener s.f)
    (hclosed : IsOpen ((stepσ s c).hom.left.base ⁻¹' Z.V \ transportedSupport s c Z))
    (hgerm : ∀ x' ∈ transportedSupport s c Z, ∀ Z₁ : LocalFlattener (nextWith s c).f,
      x' ∈ Z₁.support → ∀ᶠ y' in 𝓝 x', (y' ∈ transportedSupport s c Z ↔ y' ∈ Z₁.support)) :
    ∃ Z' : LocalFlattener (nextWith s c).f, Z'.support = transportedSupport s c Z := by
  have hf' : IsProperMap (nextWith s c).f.hom.left.base := by
    have := c.finiteType
    exact HironakaG10ChowOneStepStrictTransform.strictP_isProperMap c.B c.b c.dense s.f hf
  obtain ⟨Z', -, hZ', -⟩ := exists_localFlattener_of_support_germs_persistent (nextWith s c).f hf'
    _ _ ((Z.isOpen).preimage (stepσ s c).hom.left.base.hom.continuous)
    (transportedSupport_subset s c Z) hclosed hgerm
  exact ⟨Z', hZ'⟩

end

end Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm
