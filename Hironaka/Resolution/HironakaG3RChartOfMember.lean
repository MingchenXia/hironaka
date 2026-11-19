import Hironaka.Resolution.HironakaG3RGluedEmbedded
import Hironaka.Resolution.HironakaG3RFinal

/-! # G3: every member of a class with comparisons is a chart of the glued space

Lane G3 (run 0080, round 4).  Blueprint: `hironaka-g3-r-chart-of-member.tex`.  Notes:
`work/hironaka-resume-20261111/G3/G3-TARGET-A.md`.

* **`chartOfMember`** (generic): if `P : X' → X` is covered by charts of a class `𝒞` with comparisons, then EVERY member
  `T` of `𝒞` over ANY open `U` is a chart: its last stage is biholomorphic to `P⁻¹ U` over `U`.  The biholomorphism is
  glued from the local maps `φ_c ∘ η` (`η` a comparison of `T` with a chart `c`); the local maps agree by the rigidity of
  the glued data, the inverse maps agree by the rigidity of `T`.
* **`canonicalClass M`** (the members of target (A)), `toTowerChart`, `toGluedChart`,
  `hasComparisons_canonicalClass`; **`exists_gluedChart_of_subset_isCompact`**: a glued canonical resolution is, over every
  open set contained in a compact set (e.g. relatively compact), a SINGLE finite canonical resolution.
* **`exists_embeddedChart_of_subset_isCompact`**: the same for glued embedded resolutions (a single stopped canonical
  prefix over every open set contained in a compact set).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function
open scoped Topology Manifold ContDiff

universe u

namespace Hironaka.HironakaG3RChartOfMember

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MarkedIdeals MarkedIdeals.MarkedIdeal
  CanonicalCentres MaxLocusLocal
  RestrictEmptyTower HironakaG3RGluedUniqueness HironakaG3RTowerClass
open MarkedIdealBiholomorphism.MarkedIdeal (pullback)
open ResolutionInvariantSpec (IsInvDomain IsCanonical)

variable {n : ℕ}

/-- `val ∘ e ∘ g` has the exceptional points of `g`, for `e` a biholomorphism onto an open set. -/
theorem exceptionalLocus_val_diffeo_comp {A : Type u} [TopologicalSpace A] [ChartedSpace (ComplexModel n) A]
    [IsComplexManifold n A] {B C : CMfd.{u} n} {V' : Opens C}
    (e : B ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V') {g : A → B}
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) :
    exceptionalLocus n (fun a => ((e (g a) : V') : C)) = exceptionalLocus n g := by
  change exceptionalLocus n (Subtype.val ∘ (e ∘ g)) = _
  rw [exceptionalLocus_val_comp (e.contMDiff.comp hg), exceptionalLocus_diffeo_comp _ hg]

/-- The saturated open `P⁻¹ U`. -/
def satOpen {X X' : CMfd.{u} n} {P : X' → X} (hP : Continuous P) (U : Opens X) : Opens X' :=
  ⟨P ⁻¹' (U : Set X), U.isOpen.preimage hP⟩

/-- The part of a chart over `U`. -/
def gDom {X X' : CMfd.{u} n} {𝒞 : LocalTowerClass X} {P : X' → X} (hP : Continuous P) (U : Opens X)
    (c : TowerChart 𝒞 X' P) : Opens X' :=
  satOpen hP U ⊓ c.V

section Member

variable {X : CMfd.{u} n} {𝒞 : LocalTowerClass X} (hcmp : HasComparisons 𝒞) {X' : CMfd.{u} n} {P : X' → X}
  {U : Opens X} {Y : CMfd.{u} n} (T : BlowupTower (CMfd.of (n := n) U) Y) (hT : 𝒞 U Y T)

/-- The part of the last stage of `T` over `U ∩ U_c`. -/
def cmpDom (c : TowerChart 𝒞 X' P) : Opens Y := openPreimage T (nestedOpens U (U ⊓ c.U))

theorem mem_cmpDom {c : TowerChart 𝒞 X' P} {y : Y} : y ∈ cmpDom T c ↔ ((T.proj y : U) : X) ∈ c.U :=
  ⟨fun h => h.2, fun h => ⟨(T.proj y).2, h⟩⟩

/-- A chosen comparison of the member `T` with the tower of a chart. -/
def memberCmp (c : TowerChart 𝒞 X' P) :
    CMfd.of (n := n) (cmpDom T c) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
      CMfd.of (n := n) (openPreimage c.T (nestedOpens c.U (U ⊓ c.U))) :=
  (hcmp U c.U Y c.Y T c.T hT c.mem).choose

theorem memberCmp_proj (c : TowerChart 𝒞 X' P) (y : cmpDom T c) :
    ((c.T.proj (memberCmp hcmp T hT c y).1 : c.U) : X) = ((T.proj y.1 : U) : X) :=
  (hcmp U c.U Y c.Y T c.T hT c.mem).choose_spec y

/-- The local map `φ_c ∘ η` into `X'`. -/
def localF (c : TowerChart 𝒞 X' P) (y : cmpDom T c) : X' :=
  ((c.φ (memberCmp hcmp T hT c y).1 : c.V) : X')

theorem proj_localF (c : TowerChart 𝒞 X' P) (y : cmpDom T c) : P (localF hcmp T hT c y) = ((T.proj y.1 : U) : X) :=
  (c.proj_φ _).trans (memberCmp_proj hcmp T hT c y)

theorem contMDiff_localF (c : TowerChart 𝒞 X' P) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (localF hcmp T hT c) :=
  contMDiff_subtype_val.comp (c.φ.contMDiff.comp (contMDiff_subtype_val.comp (memberCmp hcmp T hT c).contMDiff))

theorem exceptionalLocus_localF (c : TowerChart 𝒞 X' P) : exceptionalLocus n (localF hcmp T hT c) = ∅ := by
  have hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun y : cmpDom T c => ((memberCmp hcmp T hT c y : openPreimage c.T (nestedOpens c.U (U ⊓ c.U))) : c.Y)) :=
    contMDiff_subtype_val.comp (memberCmp hcmp T hT c).contMDiff
  change exceptionalLocus n (fun y : cmpDom T c => ((c.φ ((memberCmp hcmp T hT c y :
    openPreimage c.T (nestedOpens c.U (U ⊓ c.U))) : c.Y) : c.V) : X')) = ∅
  refine (exceptionalLocus_val_diffeo_comp c.φ hg).trans ?_
  change exceptionalLocus n (Subtype.val ∘ (memberCmp hcmp T hT c)) = ∅
  rw [exceptionalLocus_val_comp (memberCmp hcmp T hT c).contMDiff]
  exact eq_empty_of_forall_notMem (MarkedIdealTowerTransport.notMem_exceptionalLocus _)

variable (hch : ∀ x, ∃ c : TowerChart 𝒞 X' P, x ∈ c.U)

/-- **The map of the member into the glued space**: at `y`, the local map of the chosen chart at `T.proj y`. -/
def memberMap (y : Y) : X' :=
  localF hcmp T hT (hch (T.proj y : X)).choose ⟨y, mem_cmpDom T |>.mpr (hch (T.proj y : X)).choose_spec⟩

theorem memberMap_eq (c : TowerChart 𝒞 X' P) (y : Y) (hy : y ∈ cmpDom T c) :
    memberMap hcmp T hT hch y = localF hcmp T hT c ⟨y, hy⟩ := by
  set c₀ := (hch (T.proj y : X)).choose
  have hy₀ : y ∈ cmpDom T c₀ := (mem_cmpDom T).mpr (hch (T.proj y : X)).choose_spec
  let O : Opens Y := cmpDom T c₀ ⊓ cmpDom T c
  have hi₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun o : O => (⟨o, o.2.1⟩ : cmpDom T c₀)) :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val _
  have hi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun o : O => (⟨o, o.2.2⟩ : cmpDom T c)) :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val _
  have hexc : exceptionalLocus n (localF hcmp T hT c₀ ∘ fun o : O => (⟨o, o.2.1⟩ : cmpDom T c₀)) = ∅ := by
    rw [exceptionalLocus_comp ((contMDiff_localF hcmp T hT c₀).mdifferentiable (by simp))
      (hi₀.mdifferentiable (by simp)), exceptionalLocus_localF, preimage_empty, union_empty]
    refine (exceptionalLocus_opens_mk contMDiff_subtype_val _).trans ?_
    exact HironakaBaseChange.exceptionalLocus_val
  have h := HironakaG3RTowerClass.eq_of_proj_eq_of_charts (Z := CMfd.of (n := n) O) hch _ _
    ((contMDiff_localF hcmp T hT c₀).comp hi₀) ((contMDiff_localF hcmp T hT c).comp hi) hexc
    (fun o => (proj_localF hcmp T hT c₀ ⟨o, o.2.1⟩).trans (proj_localF hcmp T hT c ⟨o, o.2.2⟩).symm)
  exact congrFun h ⟨y, hy₀, hy⟩

theorem proj_memberMap (y : Y) : P (memberMap hcmp T hT hch y) = ((T.proj y : U) : X) :=
  proj_localF hcmp T hT _ _

theorem contMDiff_memberMap :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (memberMap hcmp T hT hch) := by
  intro y
  obtain ⟨c, hc⟩ := hch (T.proj y : X)
  have hy : y ∈ cmpDom T c := (mem_cmpDom T).mpr hc
  have hO : (fun o : cmpDom T c => memberMap hcmp T hT hch o) = localF hcmp T hT c :=
    funext fun o => memberMap_eq hcmp T hT hch c o o.2
  have h := contMDiff_localF hcmp T hT c ⟨y, hy⟩
  rw [← hO] at h
  exact contMDiffAt_subtype_iff.mp h

variable (hP : Continuous P)


theorem memberMap_mem (y : Y) : memberMap hcmp T hT hch y ∈ satOpen hP U := by
  show P (memberMap hcmp T hT hch y) ∈ U
  rw [proj_memberMap hcmp T hT hch y]
  exact (T.proj y).2


theorem symm_mem (c : TowerChart 𝒞 X' P) (z : gDom hP U c) :
    c.φ.symm ⟨z, z.2.2⟩ ∈ openPreimage c.T (nestedOpens c.U (U ⊓ c.U)) := by
  show ((c.T.proj (c.φ.symm ⟨z, z.2.2⟩) : c.U) : X) ∈ (U ⊓ c.U : Opens X)
  rw [c.proj_symm]
  have hzV : (z : X') ∈ (c.V : Set X') := z.2.2
  rw [c.V_eq] at hzV
  exact ⟨z.2.1, hzV⟩

/-- The local inverse `η⁻¹ ∘ φ_c⁻¹` on the part of a chart over `U`. -/
def localG (c : TowerChart 𝒞 X' P) (z : gDom hP U c) : Y :=
  (((memberCmp hcmp T hT c).symm ⟨c.φ.symm ⟨z, z.2.2⟩, symm_mem hP c z⟩ : cmpDom T c) : Y)

theorem proj_localG (c : TowerChart 𝒞 X' P) (z : gDom hP U c) :
    ((T.proj (localG hcmp T hT hP c z) : U) : X) = P z := by
  have h := memberCmp_proj hcmp T hT c ((memberCmp hcmp T hT c).symm ⟨c.φ.symm ⟨z, z.2.2⟩, symm_mem hP c z⟩)
  rw [Diffeomorph.apply_symm_apply] at h
  exact h.symm.trans (c.proj_symm _)

theorem contMDiff_localG (c : TowerChart 𝒞 X' P) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (localG hcmp T hT hP c) ∧
      exceptionalLocus n (localG hcmp T hT hP c) = ∅ := by
  have hk₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun z : gDom hP U c => (⟨z, z.2.2⟩ : c.V)) := BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val _
  have hp : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun z : gDom hP U c => c.φ.symm ⟨z, z.2.2⟩) := c.φ.symm.contMDiff.comp hk₁
  have hk₂ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun z : gDom hP U c => (⟨c.φ.symm ⟨z, z.2.2⟩, symm_mem hP c z⟩ :
        openPreimage c.T (nestedOpens c.U (U ⊓ c.U)))) := BlowupRestrictOpen.contMDiff_opens_mk hp _
  have h3 := (memberCmp hcmp T hT c).symm.contMDiff.comp hk₂
  refine ⟨contMDiff_subtype_val.comp h3, ?_⟩
  change exceptionalLocus n (Subtype.val ∘ ((memberCmp hcmp T hT c).symm ∘
    fun z : gDom hP U c => (⟨c.φ.symm ⟨z, z.2.2⟩, symm_mem hP c z⟩ :
      openPreimage c.T (nestedOpens c.U (U ⊓ c.U))))) = ∅
  rw [exceptionalLocus_val_comp h3, exceptionalLocus_diffeo_comp _ hk₂]
  refine (exceptionalLocus_opens_mk hp _).trans ?_
  change exceptionalLocus n (c.φ.symm ∘ fun z : gDom hP U c => (⟨z, z.2.2⟩ : c.V)) = ∅
  rw [exceptionalLocus_diffeo_comp _ hk₁]
  refine (exceptionalLocus_opens_mk contMDiff_subtype_val _).trans ?_
  exact HironakaBaseChange.exceptionalLocus_val

/-- **The inverse map** `P⁻¹ U → Y`: at `z`, the local inverse of the chosen chart at `P z`. -/
def memberInv (z : satOpen hP U) : Y :=
  localG hcmp T hT hP (hch (P z)).choose ⟨z, z.2, (hch (P z)).choose.mem_V (hch (P z)).choose_spec⟩

theorem memberInv_eq (c : TowerChart 𝒞 X' P) (z : satOpen hP U) (hz : (z : X') ∈ c.V) :
    memberInv hcmp T hT hch hP z = localG hcmp T hT hP c ⟨z, z.2, hz⟩ := by
  set c₀ := (hch (P z)).choose
  have hz₀ : (z : X') ∈ c₀.V := c₀.mem_V (hch (P z)).choose_spec
  let O : Opens X' := gDom hP U c₀ ⊓ gDom hP U c
  have hi₀ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun o : O => (⟨o, o.2.1⟩ : gDom hP U c₀)) :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val _
  have hi : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun o : O => (⟨o, o.2.2⟩ : gDom hP U c)) :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val _
  obtain ⟨hl₀, he₀⟩ := contMDiff_localG hcmp T hT hP c₀
  obtain ⟨hl, -⟩ := contMDiff_localG hcmp T hT hP c
  have hexc : exceptionalLocus n (localG hcmp T hT hP c₀ ∘ fun o : O => (⟨o, o.2.1⟩ : gDom hP U c₀)) = ∅ := by
    rw [exceptionalLocus_comp (hl₀.mdifferentiable (by simp)) (hi₀.mdifferentiable (by simp)), he₀, preimage_empty,
      union_empty]
    refine (exceptionalLocus_opens_mk contMDiff_subtype_val _).trans ?_
    exact HironakaBaseChange.exceptionalLocus_val
  have h := eq_of_proj_eq T (Z := CMfd.of (n := n) O) _ _ (hl₀.comp hi₀) (hl.comp hi) (by rw [hexc, interior_empty])
    (fun o => Subtype.ext ((proj_localG hcmp T hT hP c₀ ⟨o, o.2.1⟩).trans
      (proj_localG hcmp T hT hP c ⟨o, o.2.2⟩).symm))
  exact congrFun h ⟨z, ⟨z.2, hz₀⟩, ⟨z.2, hz⟩⟩

theorem proj_memberInv (z : satOpen hP U) :
    ((T.proj (memberInv hcmp T hT hch hP z) : U) : X) = P z :=
  proj_localG hcmp T hT hP _ _

theorem contMDiff_memberInv :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (memberInv hcmp T hT hch hP) := by
  intro z
  obtain ⟨c, hc⟩ := hch (P z)
  have hz : (z : X') ∈ c.V := c.mem_V hc
  let O : Opens (satOpen hP U) := ⟨Subtype.val ⁻¹' (c.V : Set X'), c.V.isOpen.preimage continuous_subtype_val⟩
  have hk : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun o : O => (⟨(o : satOpen hP U), (o : satOpen hP U).2, o.2⟩ : gDom hP U c)) :=
    BlowupRestrictOpen.contMDiff_opens_mk (V := gDom hP U c) (f := fun o : O => ((o : satOpen hP U) : X'))
      (contMDiff_subtype_val.comp contMDiff_subtype_val) (fun o => ⟨(o : satOpen hP U).2, o.2⟩)
  have hO : (fun o : O => memberInv hcmp T hT hch hP o) =
      localG hcmp T hT hP c ∘ fun o : O => (⟨(o : satOpen hP U), (o : satOpen hP U).2, o.2⟩ : gDom hP U c) :=
    funext fun o => memberInv_eq hcmp T hT hch hP c o o.2
  have h := ((contMDiff_localG hcmp T hT hP c).1.comp hk) ⟨z, hz⟩
  rw [← hO] at h
  exact contMDiffAt_subtype_iff.mp h

theorem memberInv_memberMap (y : Y) :
    memberInv hcmp T hT hch hP ⟨memberMap hcmp T hT hch y, memberMap_mem hcmp T hT hch hP y⟩ = y := by
  have hF : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (fun y : Y => (⟨memberMap hcmp T hT hch y, memberMap_mem hcmp T hT hch hP y⟩ : satOpen hP U)) :=
    BlowupRestrictOpen.contMDiff_opens_mk (contMDiff_memberMap hcmp T hT hch) _
  have h := eq_of_proj_eq T id (fun y => memberInv hcmp T hT hch hP
      ⟨memberMap hcmp T hT hch y, memberMap_mem hcmp T hT hch hP y⟩) contMDiff_id
    ((contMDiff_memberInv hcmp T hT hch hP).comp hF) (by rw [exceptionalLocus_id, interior_empty])
    (fun y => Subtype.ext ((proj_memberInv hcmp T hT hch hP _).trans (proj_memberMap hcmp T hT hch y)).symm)
  exact (congrFun h y).symm

theorem memberMap_memberInv (z : satOpen hP U) :
    memberMap hcmp T hT hch (memberInv hcmp T hT hch hP z) = z := by
  have h := HironakaG3RTowerClass.eq_of_proj_eq_of_charts (Z := CMfd.of (n := n) (satOpen hP U)) hch
    Subtype.val (fun z => memberMap hcmp T hT hch (memberInv hcmp T hT hch hP z)) contMDiff_subtype_val
    ((contMDiff_memberMap hcmp T hT hch).comp (contMDiff_memberInv hcmp T hT hch hP))
    HironakaBaseChange.exceptionalLocus_val
    (fun z => ((proj_memberMap hcmp T hT hch _).trans (proj_memberInv hcmp T hT hch hP z)).symm)
  exact (congrFun h z).symm

/-- **The member's last stage is biholomorphic to `P⁻¹ U`.** -/
def memberDiffeo : Y ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (satOpen hP U) where
  toFun y := ⟨memberMap hcmp T hT hch y, memberMap_mem hcmp T hT hch hP y⟩
  invFun := memberInv hcmp T hT hch hP
  left_inv := memberInv_memberMap hcmp T hT hch hP
  right_inv z := Subtype.ext (memberMap_memberInv hcmp T hT hch hP z)
  contMDiff_toFun := BlowupRestrictOpen.contMDiff_opens_mk (contMDiff_memberMap hcmp T hT hch) _
  contMDiff_invFun := contMDiff_memberInv hcmp T hT hch hP

/-- **Every member is a chart**: for a class with comparisons covering the base of `P` by charts, a member `T` over `U`
is a chart of `P` with base `U` and tower `T`. -/
def chartOfMember : TowerChart 𝒞 X' P where
  U := U
  Y := Y
  T := T
  mem := hT
  V := satOpen hP U
  V_eq := rfl
  φ := memberDiffeo hcmp T hT hch hP
  proj_φ y := proj_memberMap hcmp T hT hch y

theorem chartOfMember_U : (chartOfMember hcmp T hT hch hP).U = U := rfl

end Member

/-! ### Target (A): a single canonical resolution over every relatively compact open set -/

section Canonical

variable {X : CMfd.{u} n}

/-- **The canonical class of `M`**: canonical segments of `M|_U` with empty final cosupport. -/
def canonicalClass (M : MarkedIdeal n X) : LocalTowerClass X := fun U _ T =>
  IsCanonical (pullback (Subtype.val : U → X) M) ((canonicalInvariant n).inv (pullback (Subtype.val : U → X) M)) T ∧
    IsGeoResolution (pullback (Subtype.val : U → X) M) T

theorem hasComparisons_canonicalClass {M : MarkedIdeal n X} (hM : IsInvDomain n M) :
    HasComparisons (canonicalClass M) := fun _ _ _ _ T₁ T₂ h₁ h₂ =>
  ⟨HironakaOriginalTerminalOverlapComparison.commonOpenTerminalComparison M hM inf_le_left inf_le_right T₁ T₂ h₁.1 h₂.1
      h₁.2 h₂.2,
    HironakaOriginalTerminalOverlapComparison.commonOpenTerminalComparison_proj M hM inf_le_left inf_le_right T₁ T₂ h₁.1
      h₂.1 h₁.2 h₂.2⟩

variable {M : MarkedIdeal n X} {X' : CMfd.{u} n} {P : X' → X}

/-- A chart of a glued canonical resolution is a chart for the canonical class. -/
def toTowerChart (c : GluedChart M X' P) : TowerChart (canonicalClass M) X' P :=
  ⟨c.U, c.Y, c.T, ⟨c.canonical, c.resolution⟩, c.V, c.V_eq, c.φ, c.proj_φ⟩

/-- A chart for the canonical class is a chart of a glued canonical resolution. -/
def toGluedChart (c : TowerChart (canonicalClass M) X' P) : GluedChart M X' P :=
  ⟨c.U, c.Y, c.T, c.mem.1, c.mem.2, c.V, c.V_eq, c.φ, c.proj_φ⟩

/-- **A glued canonical resolution is a single finite canonical resolution over every open set contained in a compact
set**: for such an open `U` there is a chart with base exactly `U`. -/
theorem exists_gluedChart_of_subset_isCompact (hM : IsInvDomain n M) (h : IsGluedCanonicalResolution M X' P)
    (U : Opens X) {K : Set X} (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) : ∃ c : GluedChart M X' P, c.U = U := by
  obtain ⟨Y, T, hc, hr⟩ := HironakaRelativelyCompact.exists_isCanonical_resolution_of_subset_isCompact
    (canonicalInvariant n) hM hK U hUK
  have hch : ∀ x, ∃ c : TowerChart (canonicalClass M) X' P, x ∈ c.U := fun x => by
    obtain ⟨c, hc⟩ := h.exists_chart x
    exact ⟨toTowerChart c, hc⟩
  exact ⟨toGluedChart (chartOfMember (hasComparisons_canonicalClass hM) T ⟨hc, hr⟩ hch h.1.continuous), rfl⟩

end Canonical

/-! ### Glued embedded resolutions: a single stopped prefix over every relatively compact open set -/

section Embedded

open Hironaka.NonKahlerLocus Hironaka.HolomorphicIdealSheaves HironakaG3RGluedEmbedded HironakaG3RStoppedOverlap
open EmbeddedFromResolution (regularOpen regularAtDim_of_mem_regularOpen isInvDomain_vanishingIdeal_of_dim_lt)

variable {X : CMfd.{u} n}

/-- **A glued embedded resolution is a single stopped canonical prefix over every open set contained in a compact set.** -/
theorem exists_embeddedChart_of_subset_isCompact {V : ClosedIrreducibleAnalyticSubvariety n X} (hV : V.dim < n)
    {X' : CMfd.{u} n} {P : X' → X} (h : IsGluedEmbeddedResolution V X' P) (U : Opens X) {K : Set X}
    (hK : IsCompact K) (hUK : (U : Set X) ⊆ K) : ∃ c : TowerChart (embeddedClass V) X' P, c.U = U := by
  have hdom : IsInvDomain n (⟨univ, [], vanishingIdeal (n := n) V.carrier, 1⟩ : MarkedIdeal n X) :=
    isInvDomain_vanishingIdeal_of_dim_lt le_rfl V hV
      (CartanIrreducible.cartanCoherence V.carrier V.irreducible_carrier.analytic)
  have hcmp : HasComparisons (embeddedClass V) :=
    hasComparisons_stoppedClass V.isClosed_carrier (regularOpen V) (d := V.dim)
      (fun x hx => regularAtDim_of_mem_regularOpen hx x.2)
      (HironakaEmbeddedResolutionLocal.subset_closure_inter_regularOpen V) hdom
  obtain ⟨Y, T, hc, hr⟩ := HironakaRelativelyCompact.exists_isCanonical_resolution_of_subset_isCompact
    (canonicalInvariant n) hdom hK U hUK
  have hmem : ∃ (Y' : CMfd.{u} n) (S : BlowupTower (CMfd.of (n := n) U) Y'), embeddedClass V U Y' S := by
    by_cases ha : CentresAvoid (nestedOpens U (regularOpen V)) T
    · exact ⟨Y, T, hc, ha, Or.inr hr⟩
    · obtain ⟨Y', T', -, -, h1, h2, c, hc', hcU⟩ :=
        EmbeddedFromResolution.exists_first_centre _ _ (nestedOpens U (regularOpen V)) T hc ha
      exact ⟨Y', T', h1, h2, Or.inl ⟨c, hc', hcU⟩⟩
  obtain ⟨Y', S, hS⟩ := hmem
  exact ⟨chartOfMember hcmp S hS h.2.2.2 h.1.continuous, rfl⟩

end Embedded

end

end Hironaka.HironakaG3RChartOfMember
