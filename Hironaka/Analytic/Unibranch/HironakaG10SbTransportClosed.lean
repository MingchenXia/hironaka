import Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm
import Hironaka.Analytic.Unibranch.HironakaG10ActualBlowupStrictMembership

/-!
# The transported support of Lemma 4.4.5 is closed (G10-03-09.b)

Lane G10SB, run 0081.  Consumer: `HironakaG10SbFlattenerSupportGerm.exists_localFlattener_transport_of_support_germs`
(hypothesis `hclosed`), towards lane G10RD's `hT` (Hironaka 1975 Lemma 4.4.5, printed pp. 537–538).

For a local flattener `Z` of `f` and one admissible blowup step `σ`, the transported set
`T(Z) = {x' | σ x' ∈ |Z| ∧ OnStrictTransform σ x' (germFlattener f (σ x')) (centreIdeal c (σ x'))}`
is closed in `σ⁻¹ V` (`isOpen_preimage_diff_transportedSupport`).  At a point of `σ⁻¹ V` off `T(Z)` either
`σ x'` is off `|Z|` (open condition), or the germ strict ideal is the unit ideal; one relation
`1 = Σ cᵢ h'ᵢ`, `σ^♯ hᵢ = Gᵏⁱ h'ᵢ`, `hᵢ ∈ I_Z ⊓ I_D^{kᵢ}` spreads to a neighbourhood, because
(`Spreads`) every element of the whole-fibre flattener at a support point and every element of a power of the centre
ideal is the germ of ONE section whose germs stay in the family nearby, and the local exceptional generator of
`HironakaG10ActualBlowupStrictMembership.exists_local_projection_strict_criterion` is a section.

No named input.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set TopologicalSpace CategoryTheory Opposite AlgebraicGeometry Filter
open scoped Topology

namespace Hironaka.Analytic.Unibranch.HironakaG10SbTransportClosed

open Hironaka HironakaG10PNIdealFamily HironakaG10HirIdealGerms
  HironakaSingularModuleSheafStalk HironakaG10ChowArtinReesCentre
open Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener Hironaka.Analytic.Unibranch.HironakaG10ChowLeavingRounds
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm Hironaka.Analytic.Unibranch.HironakaG10ActualBlowupStrictMembership

noncomputable section

/-! ### Germs of sections that stay in an ideal family -/

section Spread

variable {T : LocallyRingedSpace.{0}}

theorem germ_res_hom {U V : Opens T} (i : U ⟶ V) (x : T) (hx : x ∈ U)
    (s : T.presheaf.obj (op V)) :
    (T.presheaf.germ U x hx).hom ((T.presheaf.map i.op).hom s) =
      (T.presheaf.germ V x (i.le hx)).hom s :=
  TopCat.Presheaf.germ_res_apply T.presheaf i x hx s

/-- `a` is the germ at `x` of one section whose germs lie in the family `F` at every point of its open. -/
def Spreads (F : ∀ z : T, Ideal (T.presheaf.stalk z)) (x : T) (a : T.presheaf.stalk x) : Prop :=
  ∃ (U : Opens T) (hx : x ∈ U) (s : T.presheaf.obj (op U)),
    (T.presheaf.germ U x hx).hom s = a ∧ ∀ (z : T) (hz : z ∈ U), (T.presheaf.germ U z hz).hom s ∈ F z

theorem exists_section (x : T) (a : T.presheaf.stalk x) :
    ∃ (U : Opens T) (hx : x ∈ U) (s : T.presheaf.obj (op U)), (T.presheaf.germ U x hx).hom s = a :=
  TopCat.Presheaf.exists_germ_eq T.presheaf a

theorem spreads_restrict {F : ∀ z : T, Ideal (T.presheaf.stalk z)}
    {U : Opens T} {s : T.presheaf.obj (op U)}
    (hs : ∀ (z : T) (hz : z ∈ U), (T.presheaf.germ U z hz).hom s ∈ F z)
    (W : Opens T) (hW : W ≤ U) (z : T) (hz : z ∈ W) :
    (T.presheaf.germ W z hz).hom ((T.presheaf.map (homOfLE hW).op).hom s) ∈ F z := by
  rw [germ_res_hom]
  exact hs z _

theorem spreads_top (x : T) (a : T.presheaf.stalk x) : Spreads (fun _ => ⊤) x a := by
  obtain ⟨U, hx, s, hs⟩ := exists_section x a
  exact ⟨U, hx, s, hs, fun _ _ => Submodule.mem_top⟩

theorem spreads_zero (F : ∀ z : T, Ideal (T.presheaf.stalk z)) (x : T) : Spreads F x 0 :=
  ⟨⊤, trivial, 0, map_zero _, fun z _ => by rw [map_zero]; exact (F z).zero_mem⟩

theorem spreads_add {F : ∀ z : T, Ideal (T.presheaf.stalk z)} {x : T} {a b : T.presheaf.stalk x}
    (ha : Spreads F x a) (hb : Spreads F x b) : Spreads F x (a + b) := by
  obtain ⟨U, hxU, s, rfl, hs⟩ := ha
  obtain ⟨V, hxV, t, rfl, ht⟩ := hb
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, (T.presheaf.map (homOfLE inf_le_left).op).hom s +
    (T.presheaf.map (homOfLE inf_le_right).op).hom t, ?_, fun z hz => ?_⟩
  · rw [map_add, germ_res_hom, germ_res_hom]
  · rw [map_add]
    exact (F z).add_mem (spreads_restrict hs _ inf_le_left z hz)
      (spreads_restrict ht _ inf_le_right z hz)

theorem spreads_mul_left {F : ∀ z : T, Ideal (T.presheaf.stalk z)} {x : T}
    (r : T.presheaf.stalk x) {a : T.presheaf.stalk x} (ha : Spreads F x a) :
    Spreads F x (r * a) := by
  obtain ⟨U, hxU, s, rfl, hs⟩ := ha
  obtain ⟨V, hxV, t, rfl⟩ := exists_section x r
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, (T.presheaf.map (homOfLE inf_le_right).op).hom t *
    (T.presheaf.map (homOfLE inf_le_left).op).hom s, ?_, fun z hz => ?_⟩
  · rw [map_mul, germ_res_hom, germ_res_hom]
  · rw [map_mul]
    exact (F z).mul_mem_left _ (spreads_restrict hs _ inf_le_left z hz)

theorem spreads_of_mem_span {F : ∀ z : T, Ideal (T.presheaf.stalk z)} {x : T}
    {S : Set (T.presheaf.stalk x)} (hS : ∀ a ∈ S, Spreads F x a) :
    ∀ a ∈ Ideal.span S, Spreads F x a := by
  intro a ha
  induction ha using Submodule.span_induction with
  | mem a h => exact hS a h
  | zero => exact spreads_zero F x
  | add a b _ _ iha ihb => exact spreads_add iha ihb
  | smul r a _ ih => exact spreads_mul_left r ih

theorem spreads_mul {F G : ∀ z : T, Ideal (T.presheaf.stalk z)} {x : T}
    {a b : T.presheaf.stalk x} (ha : Spreads F x a) (hb : Spreads G x b) :
    Spreads (fun z => F z * G z) x (a * b) := by
  obtain ⟨U, hxU, s, rfl, hs⟩ := ha
  obtain ⟨V, hxV, t, rfl, ht⟩ := hb
  refine ⟨U ⊓ V, ⟨hxU, hxV⟩, (T.presheaf.map (homOfLE inf_le_left).op).hom s *
    (T.presheaf.map (homOfLE inf_le_right).op).hom t, ?_, fun z hz => ?_⟩
  · rw [map_mul, germ_res_hom, germ_res_hom]
  · rw [map_mul]
    exact Ideal.mul_mem_mul (spreads_restrict hs _ inf_le_left z hz)
      (spreads_restrict ht _ inf_le_right z hz)

theorem spreads_pow {F : ∀ z : T, Ideal (T.presheaf.stalk z)} {x : T}
    (hF : ∀ a ∈ F x, Spreads F x a) : ∀ k : ℕ, ∀ a ∈ F x ^ k, Spreads (fun z => F z ^ k) x a := by
  intro k
  induction k with
  | zero =>
    intro a _
    have h := spreads_top (T := T) x a
    simpa only [pow_zero, Ideal.one_eq_top] using h
  | succ k ih =>
    intro a ha
    rw [pow_succ] at ha
    have hfam : (fun z => F z ^ (k + 1)) = fun z => F z ^ k * F z := by
      funext z
      rw [pow_succ]
    rw [hfam]
    refine Submodule.mul_induction_on ha (fun i hi j hj => spreads_mul (ih i hi) (hF j hj)) ?_
    exact fun a b iha ihb => spreads_add iha ihb

theorem spreads_inf {F G : ∀ z : T, Ideal (T.presheaf.stalk z)} {x : T} {a : T.presheaf.stalk x}
    (hF : Spreads F x a) (hG : Spreads G x a) : Spreads (fun z => F z ⊓ G z) x a := by
  obtain ⟨U, hxU, s, hsa, hs⟩ := hF
  obtain ⟨V, hxV, t, hta, ht⟩ := hG
  have heq : T.presheaf.germ U x hxU s = T.presheaf.germ V x hxV t := hsa.trans hta.symm
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq T.presheaf x hxU hxV s t heq
  refine ⟨W, hxW, (T.presheaf.map iU.op).hom s, ?_, fun z hz => ⟨?_, ?_⟩⟩
  · rw [germ_res_hom]
    exact hsa
  · rw [germ_res_hom]
    exact hs z _
  · have h' : (T.presheaf.map iU.op).hom s = (T.presheaf.map iV.op).hom t := hW
    rw [h', germ_res_hom]
    exact ht z _

end Spread

/-! ### The two families of a step spread -/

variable {X Y : SourceReducedComplexSpace} {f : Y ⟶ X}

/-- Every element of the centre ideal spreads in the centre ideal family. -/
theorem spreads_centreIdeal (c : AdmissibleCentre f) (x : X.obj.left) (d : X.obj.left.presheaf.stalk x)
    (hd : d ∈ centreIdeal c x) : Spreads (T := X.obj.left) (centreIdeal c) x d := by
  obtain ⟨β, rfl⟩ := hd
  obtain ⟨U, hxU, m, rfl⟩ := TopCat.Presheaf.exists_germ_eq c.B.val.presheaf β
  refine ⟨U, hxU, c.b.val.app (op U) m, ?_, fun z hz => ?_⟩
  · exact (stalkInclusionLinearMap_germ X.obj.left.toSheafedSpace.sheaf c.B c.b x U hxU m).symm
  · exact ⟨TopCat.Presheaf.germ c.B.val.presheaf U z hz m,
      stalkInclusionLinearMap_germ X.obj.left.toSheafedSpace.sheaf c.B c.b z U hz m⟩

/-- Every element of a local flattener's ideal at a point of `V` spreads in its family (near points of
`V`, where it is generated by finitely many fixed sections). -/
theorem spreads_localFlattener (Z : LocalFlattener f) (x : X.obj.left) (hx : x ∈ Z.V)
    (a : X.obj.left.presheaf.stalk x) (ha : a ∈ Z.H x) :
    Spreads (T := X.obj.left) Z.H x a := by
  obtain ⟨W, hxW, r, s, hs⟩ := Z.fg x hx
  let O : Opens X.obj.left := W ⊓ ⟨Z.V, Z.isOpen⟩
  have hgen : ∀ i, Spreads (T := X.obj.left) Z.H x
      (X.obj.left.presheaf.germ W x hxW (s i)) := by
    intro i
    refine ⟨O, ⟨hxW, hx⟩, (X.obj.left.presheaf.map (homOfLE inf_le_left).op).hom (s i), ?_,
      fun z hz => ?_⟩
    · rw [germ_res_hom]
    · rw [germ_res_hom]
      rw [hs z hz.1 hz.2]
      exact Ideal.subset_span ⟨i, rfl⟩
  rw [hs x hxW hx] at ha
  refine spreads_of_mem_span (S := Set.range fun i => X.obj.left.presheaf.germ W x hxW (s i)) ?_ a ha
  rintro _ ⟨i, rfl⟩
  exact hgen i

/-! ### Spreading equalities of germs, stalk maps and units -/

section Germs

theorem eventually_germ_eq {T : LocallyRingedSpace.{0}} {U V : Opens T} {x : T} (hxU : x ∈ U)
    (hxV : x ∈ V) (s : T.presheaf.obj (op U)) (t : T.presheaf.obj (op V))
    (h : (T.presheaf.germ U x hxU).hom s = (T.presheaf.germ V x hxV).hom t) :
    ∀ᶠ z in 𝓝 x, ∀ (hzU : z ∈ U) (hzV : z ∈ V),
      (T.presheaf.germ U z hzU).hom s = (T.presheaf.germ V z hzV).hom t := by
  obtain ⟨W, hxW, iU, iV, hW⟩ := TopCat.Presheaf.germ_eq T.presheaf x hxU hxV s t h
  filter_upwards [W.isOpen.mem_nhds hxW] with z hzW hzU hzV
  have hW' : (T.presheaf.map iU.op).hom s = (T.presheaf.map iV.op).hom t := hW
  calc (T.presheaf.germ U z hzU).hom s
      = (T.presheaf.germ W z hzW).hom ((T.presheaf.map iU.op).hom s) := (germ_res_hom iU z hzW s).symm
    _ = (T.presheaf.germ W z hzW).hom ((T.presheaf.map iV.op).hom t) := by rw [hW']
    _ = (T.presheaf.germ V z hzV).hom t := germ_res_hom iV z hzW t

theorem stalkMap_germ_hom {A B : LocallyRingedSpace.{0}} (g : A ⟶ B) (U : Opens B) (x : A)
    (hx : g.base x ∈ U) (t : B.presheaf.obj (op U)) :
    (g.stalkMap x).hom ((B.presheaf.germ U (g.base x) hx).hom t) =
      (A.presheaf.germ ((Opens.map g.base).obj U) x hx).hom ((g.c.app (op U)).hom t) :=
  LocallyRingedSpace.stalkMap_germ_apply g U x hx t

theorem exists_isUnit_of_span_eq_top {R : Type*} [CommRing R] [IsLocalRing R] {S : Set R}
    (h : Ideal.span S = ⊤) : ∃ g ∈ S, IsUnit g := by
  by_contra hne
  have hS : ∀ g ∈ S, ¬ IsUnit g := fun g hg hu => hne ⟨g, hg, hu⟩
  have hle : Ideal.span S ≤ IsLocalRing.maximalIdeal R :=
    Ideal.span_le.mpr fun g hg => (IsLocalRing.mem_maximalIdeal g).mpr (hS g hg)
  rw [h] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top (top_le_iff.mp hle)

theorem span_eq_top_of_isUnit_mem {R : Type*} [CommRing R] {S : Set R} {g : R} (hg : g ∈ S)
    (hu : IsUnit g) : Ideal.span S = ⊤ :=
  Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span hg) hu

end Germs

/-! ### The transported support is closed -/

/-- **G10-03-09.b (Closed).**  For one admissible step and a local flattener `Z`, the complement of the
transported support `T(Z)` (Lemma 4.4.5) in `σ⁻¹ V` is open. -/
theorem isOpen_preimage_diff_transportedSupport (s : Stage) (c : AdmissibleCentre s.f)
    (Z : LocalFlattener s.f) :
    IsOpen ((stepσ s c).hom.left.base ⁻¹' Z.V \ transportedSupport s c Z) := by
  have hft := c.finiteType
  rw [isOpen_iff_mem_nhds]
  rintro x' ⟨hx'V, hx'T⟩
  have hcont : Continuous (stepσ s c).hom.left.base := (stepσ s c).hom.left.base.hom.continuous
  by_cases hsupp : (stepσ s c).hom.left.base x' ∈ Z.support
  · -- the germ strict ideal is the unit ideal at `x'`
    obtain ⟨U, hxU, sG, hcrit⟩ := exists_local_projection_strict_criterion c.B c.b c.dense x'
    obtain ⟨_, _, hiff⟩ := hcrit x' hxU
    have htop : strictIdeal ((stepσ s c).hom.left.stalkMap x').hom
        (germFlattener s.f ((stepσ s c).hom.left.base x')) (centreIdeal c ((stepσ s c).hom.left.base x'))
        ((nextWith s c).X.obj.left.presheaf.germ U x' hxU sG.val) = ⊤ := by
      by_contra h
      exact hx'T ⟨hsupp, (hiff _).mpr h⟩
    obtain ⟨g, ⟨k, h, hmem, heq⟩, hgu⟩ := exists_isUnit_of_span_eq_top htop
    -- the base element spreads in `Z.H ⊓ I_D^k`
    have hhZ : h ∈ Z.H ((stepσ s c).hom.left.base x') := by
      rw [Z.H_eq_germFlattener hsupp]
      exact hmem.1
    have hspread : Spreads (T := s.X.obj.left)
        (fun z => Z.H z ⊓ centreIdeal c z ^ k) ((stepσ s c).hom.left.base x') h :=
      spreads_inf (spreads_localFlattener Z _ hsupp.1 h hhZ)
        (spreads_pow (spreads_centreIdeal c _) k h hmem.2)
    obtain ⟨U₁, hxU₁, hh, hhgerm, hhmem⟩ := hspread
    -- the new-point elements are germs of sections
    obtain ⟨V₁, hxV₁, gg, hgg⟩ := exists_section x' g
    obtain ⟨u, hu⟩ := hgu
    obtain ⟨V₂, hxV₂, ww, hww⟩ := exists_section x' (↑u⁻¹ : (nextWith s c).X.obj.left.presheaf.stalk x')
    -- the equation `σ^♯ h = G^k g` spreads
    have hE1 := eventually_germ_eq (T := (nextWith s c).X.obj.left) (U := (Opens.map
        (stepσ s c).hom.left.base).obj U₁) (V := U ⊓ V₁) hxU₁ ⟨hxU, hxV₁⟩
      (((stepσ s c).hom.left.c.app (op U₁)).hom hh)
      (((nextWith s c).X.obj.left.presheaf.map (homOfLE inf_le_left).op).hom sG.val ^ k *
        ((nextWith s c).X.obj.left.presheaf.map (homOfLE inf_le_right).op).hom gg) (by
          rw [← stalkMap_germ_hom, hhgerm, map_mul, map_pow, germ_res_hom, germ_res_hom, hgg]
          exact heq)
    -- the inverse equation `g · g⁻¹ = 1` spreads
    have hE2 := eventually_germ_eq (T := (nextWith s c).X.obj.left) (U := V₁ ⊓ V₂) (V := ⊤)
      ⟨hxV₁, hxV₂⟩ trivial
      (((nextWith s c).X.obj.left.presheaf.map (homOfLE inf_le_left).op).hom gg *
        ((nextWith s c).X.obj.left.presheaf.map (homOfLE inf_le_right).op).hom ww) 1 (by
          rw [map_mul, germ_res_hom, germ_res_hom, hgg, hww, map_one, ← hu, Units.mul_inv])
    have hU₁ : ∀ᶠ y' in 𝓝 x', (stepσ s c).hom.left.base y' ∈ U₁ :=
      hcont.continuousAt.preimage_mem_nhds (U₁.isOpen.mem_nhds hxU₁)
    filter_upwards [hE1, hE2, hU₁, U.isOpen.mem_nhds hxU, V₁.isOpen.mem_nhds hxV₁,
      V₂.isOpen.mem_nhds hxV₂, (Z.isOpen.preimage hcont).mem_nhds hx'V]
      with y' e1 e2 hy₁ hyU hyV₁ hyV₂ hyV
    refine ⟨hyV, fun hyT => ?_⟩
    obtain ⟨_, _, hiff'⟩ := hcrit y' hyU
    refine (hiff' _).mp hyT.2 ?_
    -- the germ of `gg` at `y'` is a unit in the strict set
    have e1' := e1 hy₁ ⟨hyU, hyV₁⟩
    have e2' := e2 ⟨hyV₁, hyV₂⟩ trivial
    rw [map_mul, germ_res_hom, germ_res_hom, map_one] at e2'
    rw [map_mul, map_pow, germ_res_hom, germ_res_hom, ← stalkMap_germ_hom] at e1'
    refine span_eq_top_of_isUnit_mem ⟨k, (s.X.obj.left.presheaf.germ U₁ _ hy₁).hom hh, ?_, e1'⟩
      (IsUnit.of_mul_eq_one _ e2')
    have hm := hhmem _ hy₁
    refine ⟨?_, hm.2⟩
    rw [← Z.H_eq_germFlattener hyT.1]
    exact hm.1
  · -- off the support
    have hO := Z.isOpen_inter_eq_top
    have hx'O : (stepσ s c).hom.left.base x' ∈ Z.V ∩ {x | Z.H x = ⊤} :=
      ⟨hx'V, by_contra fun h => hsupp ⟨hx'V, h⟩⟩
    filter_upwards [(hO.preimage hcont).mem_nhds hx'O] with y' hy'
    exact ⟨hy'.1, fun hT => hT.1.2 hy'.2⟩

/-- **Lemma 4.4.5 reduced to the support germs**: with (Closed) proved, G10RD's `hT` follows from the
support-germ statement (Germ) alone. -/
theorem exists_localFlattener_transport_of_germs (s : Stage)
    (hf : IsProperMap s.f.hom.left.base) (c : AdmissibleCentre s.f) (Z : LocalFlattener s.f)
    (hgerm : ∀ x' ∈ transportedSupport s c Z, ∀ Z₁ : LocalFlattener (nextWith s c).f,
      x' ∈ Z₁.support → ∀ᶠ y' in 𝓝 x', (y' ∈ transportedSupport s c Z ↔ y' ∈ Z₁.support)) :
    ∃ Z' : LocalFlattener (nextWith s c).f, Z'.support = transportedSupport s c Z :=
  exists_localFlattener_transport_of_support_germs s hf c Z
    (isOpen_preimage_diff_transportedSupport s c Z) hgerm

end

end Hironaka.Analytic.Unibranch.HironakaG10SbTransportClosed
