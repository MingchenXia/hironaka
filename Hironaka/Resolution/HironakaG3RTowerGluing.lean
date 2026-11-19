import Hironaka.Resolution.HironakaG3RGluedUniqueness
import Hironaka.Resolution.HironakaTerminalAtlasHolomorphic
import Mathlib.Topology.Gluing

/-! # G3: gluing local towers of blowups along projection-preserving comparisons

Lane G3 (run 0080, round 4).  Blueprint: `hironaka-g3-r-tower-gluing.tex`.  Notes:
`work/hironaka-resume-20261111/G3/G3-TARGET-A.md` (A-miss-3, step (ii)).

A generic form of the held gluing of terminal canonical resolutions (`HironakaOriginalTerminalAtlas`,
`HironakaOriginalTerminalManifold`, `HironakaOriginalTerminalProperProjection`,
`HironakaOriginalTerminalLocalBiholomorphism`), for ANY family of towers of blowups over an open cover of a complex
manifold `X` such that any two of them are compared over the intersection of their bases by SOME biholomorphism commuting
with the projections.  No canonicity is used: the self and cocycle conditions of the gluing come from the rigidity of towers
(`HironakaG3RGluedUniqueness.eq_of_proj_eq`), so the comparisons need not be chosen compatibly.

* **`TowerAtlas X`**: an open cover `U i` of `X`, towers `T i` over `U i`, and projection-preserving comparisons over
  `U i ∩ U j`.
* `transition`, `transition_self_apply`, `transition_cocycle` (rigidity), `glueCore` (`TopCat.GlueData.MkCore`).
* `gluedSpace`, `incl` (open embeddings), `proj` (the glued projection), `range_incl` (the range of `incl i` is the
  saturated open `proj⁻¹ (U i)`).
* `gluedSpace_t2`, `gluedSpace_secondCountable`, `chartedSpace`, `isComplexManifold`, **`manifold`** (a complex manifold),
  `contMDiff_incl`, **`contMDiff_proj`**, **`isProperMap_proj`**, **`surjective_proj`**, **`localBiholomorphism`**
  (the last stage of `T i` is biholomorphic onto `proj⁻¹ (U i)` over `U i`).
* **`exists_glued`**: the packaged existence statement.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Set Filter TopologicalSpace Function Topology IsManifold
open scoped Manifold ContDiff Topology
open CategoryTheory CategoryTheory.Limits

universe u

namespace Hironaka.HironakaG3RTowerGluing

noncomputable section

open Hironaka.BlowupSequences BlowupTowers BlowupTowerTransforms MaxLocusLocal
  HironakaTerminalAtlasTopology HironakaTerminalAtlasHolomorphic HironakaG3RGluedUniqueness

variable {n : ℕ}

/-- **A tower atlas on `X`**: an open cover `U i` of `X`, a tower of blowups `T i` over each `U i`, and for any two indices
some biholomorphism between the parts of the last stages over `U i ∩ U j` commuting with the projections to `X`. -/
structure TowerAtlas (X : CMfd.{u} n) : Type (u + 1) where
  /-- The index type. -/
  J : Type u
  /-- The open cover. -/
  U : J → Opens X
  cover : ∀ x : X, ∃ i, x ∈ U i
  /-- The last stages. -/
  Y : J → CMfd.{u} n
  /-- The local towers. -/
  T : ∀ i, BlowupTower (CMfd.of (n := n) (U i)) (Y i)
  compare : ∀ i j, ∃ η : CMfd.of (n := n) (openPreimage (T i) (nestedOpens (U i) (U i ⊓ U j)))
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (openPreimage (T j) (nestedOpens (U j) (U i ⊓ U j))),
    ∀ y, (((T j).proj (η y).val : U j) : X) = (((T i).proj y.val : U i) : X)

namespace TowerAtlas

variable {X : CMfd.{u} n} (A : TowerAtlas X)

/-! ### The transitions -/

/-- The part of the last stage of `T i` over `U i ∩ U j`. -/
def overlap (i j : A.J) : Opens (A.Y i) :=
  openPreimage (A.T i) (nestedOpens (A.U i) (A.U i ⊓ A.U j))

theorem mem_overlap {i j : A.J} {y : A.Y i} : y ∈ A.overlap i j ↔ (((A.T i).proj y : A.U i) : X) ∈ A.U j :=
  ⟨fun h => h.2, fun h => ⟨((A.T i).proj y).2, h⟩⟩

theorem overlap_comm (i j : A.J) :
    openPreimage (A.T j) (nestedOpens (A.U j) (A.U i ⊓ A.U j)) = A.overlap j i := by
  rw [overlap, inf_comm]

/-- **The transition** from the part of `Y i` over `U i ∩ U j` to the part of `Y j` over it (a chosen comparison). -/
def transition (i j : A.J) :
    CMfd.of (n := n) (A.overlap i j) ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (A.overlap j i) :=
  (A.compare i j).choose.trans (BlowupTowerIsoTail.opensCongr (A.overlap_comm i j))

theorem transition_proj (i j : A.J) (y : A.overlap i j) :
    (((A.T j).proj (A.transition i j y).val : A.U j) : X) = (((A.T i).proj y.val : A.U i) : X) :=
  (A.compare i j).choose_spec y

/-- Rigidity of the local towers, for maps whose first one has no exceptional points. -/
theorem eq_of_proj_eq' (i : A.J) {Z : CMfd.{u} n} (f g : Z → A.Y i)
    (hf : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ f)
    (hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g) (hexc : exceptionalLocus n f = ∅)
    (h : ∀ z, (((A.T i).proj (f z) : A.U i) : X) = (((A.T i).proj (g z) : A.U i) : X)) : f = g :=
  eq_of_proj_eq (A.T i) f g hf hg (by rw [hexc, interior_empty]) fun z => Subtype.ext (h z)

/-- `val ∘ e ∘ (inclusion)` has no exceptional points, for `e` a biholomorphism of open sets. -/
theorem exceptionalLocus_val_diffeo_mk {B C : CMfd.{u} n} {V : Opens B} {V' : Opens C} {O : Opens B}
    (e : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V')
    (hO : ∀ o : O, (o : B) ∈ V) :
    exceptionalLocus n (fun o : CMfd.of (n := n) O => ((e ⟨o, hO o⟩ : V') : C)) = ∅ := by
  have hk : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun o : O => (⟨o, hO o⟩ : V)) :=
    BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val _
  change exceptionalLocus n (Subtype.val ∘ (e ∘ fun o : O => (⟨o, hO o⟩ : V))) = ∅
  rw [exceptionalLocus_val_comp (e.contMDiff.comp hk), exceptionalLocus_diffeo_comp _ hk]
  refine (exceptionalLocus_opens_mk contMDiff_subtype_val _).trans ?_
  exact HironakaBaseChange.exceptionalLocus_val

theorem contMDiff_val_diffeo_mk {B C : CMfd.{u} n} {V : Opens B} {V' : Opens C} {O : Opens B}
    (e : CMfd.of (n := n) V ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V')
    (hO : ∀ o : O, (o : B) ∈ V) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (fun o : CMfd.of (n := n) O => ((e ⟨o, hO o⟩ : V') : C)) :=
  contMDiff_subtype_val.comp (e.contMDiff.comp (BlowupRestrictOpen.contMDiff_opens_mk contMDiff_subtype_val _))

theorem overlap_self (i : A.J) : A.overlap i i = ⊤ := by
  apply Opens.ext
  ext y
  exact ⟨fun _ => trivial, fun _ => A.mem_overlap.mpr ((A.T i).proj y).2⟩

theorem transition_self_apply (i : A.J) (y : A.overlap i i) : A.transition i i y = y := by
  have hO : ∀ o : (⊤ : Opens (A.overlap i i)), (o : A.overlap i i) ∈ (⊤ : Opens (A.overlap i i)) := fun o => o.2
  have h := A.eq_of_proj_eq' i (fun o : CMfd.of (n := n) (A.overlap i i) => (o : A.Y i))
    (fun o => (A.transition i i o : A.Y i)) contMDiff_subtype_val
    (contMDiff_subtype_val.comp (A.transition i i).contMDiff) HironakaBaseChange.exceptionalLocus_val
    (fun o => (A.transition_proj i i o).symm)
  exact Subtype.ext (congrFun h y).symm

theorem transition_inter (i j k : A.J) (y : A.overlap i j) (hy : (y : A.Y i) ∈ A.overlap i k) :
    (A.transition i j y : A.Y j) ∈ A.overlap j k := by
  rw [mem_overlap, transition_proj]
  exact A.mem_overlap.mp hy

theorem transition_cocycle (i j k : A.J) (y : A.overlap i j) (hy : (y : A.Y i) ∈ A.overlap i k) :
    (A.transition j k ⟨A.transition i j y, A.transition_inter i j k y hy⟩ : A.Y k) =
      (A.transition i k ⟨y, hy⟩ : A.Y k) := by
  let O : Opens (A.Y i) := A.overlap i j ⊓ A.overlap i k
  have h1 : ∀ o : O, (o : A.Y i) ∈ A.overlap i k := fun o => o.2.2
  have h2 : ∀ o : O, (o : A.Y i) ∈ A.overlap i j := fun o => o.2.1
  let g₁ : CMfd.of (n := n) O → A.Y j := fun o => (A.transition i j ⟨o, h2 o⟩ : A.Y j)
  have hg₁ : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g₁ := contMDiff_val_diffeo_mk _ h2
  have h3 : ∀ o : O, g₁ o ∈ A.overlap j k := fun o => A.transition_inter i j k ⟨o, h2 o⟩ (h1 o)
  let g : CMfd.of (n := n) O → A.Y k := fun o => (A.transition j k ⟨g₁ o, h3 o⟩ : A.Y k)
  have hg : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ g :=
    contMDiff_subtype_val.comp ((A.transition j k).contMDiff.comp (BlowupRestrictOpen.contMDiff_opens_mk hg₁ h3))
  have h := A.eq_of_proj_eq' k (fun o : CMfd.of (n := n) O => (A.transition i k ⟨o, h1 o⟩ : A.Y k)) g
    (contMDiff_val_diffeo_mk _ h1) hg (exceptionalLocus_val_diffeo_mk _ h1) fun o => by
      change _ = (((A.T k).proj (A.transition j k ⟨g₁ o, h3 o⟩ : A.Y k) : A.U k) : X)
      rw [transition_proj, transition_proj, transition_proj]
  exact (congrFun h ⟨y, y.2, hy⟩).symm

/-! ### The glued space -/

/-- The gluing data. -/
def glueCore : TopCat.GlueData.MkCore where
  J := A.J
  U i := TopCat.of (A.Y i)
  V := A.overlap
  t i j := TopCat.ofHom ⟨A.transition i j, (A.transition i j).contMDiff.continuous⟩
  V_id := A.overlap_self
  t_id i := by
    funext y
    exact A.transition_self_apply i y
  t_inter := fun {i j} k y hy => A.transition_inter i j k y hy
  cocycle := A.transition_cocycle

/-- The glue data. -/
def glueData : TopCat.GlueData := TopCat.GlueData.mk' A.glueCore

/-- **The glued space.** -/
def gluedSpace : TopCat := A.glueData.glued

/-- The inclusion of the last stage of `T i`. -/
def incl (i : A.J) : A.Y i → A.gluedSpace := A.glueData.ι i

theorem isOpenEmbedding_incl (i : A.J) : IsOpenEmbedding (A.incl i) := A.glueData.ι_isOpenEmbedding i

theorem incl_jointly_surjective (z : A.gluedSpace) : ∃ (i : A.J) (y : A.Y i), A.incl i y = z :=
  A.glueData.ι_jointly_surjective z

/-- The local projection of `T i` to `X`. -/
def localProj (i : A.J) : ContinuousMap (A.Y i) X :=
  ⟨fun y => (((A.T i).proj y : A.U i) : X), continuous_subtype_val.comp (A.T i).contMDiff_proj.continuous⟩

theorem localProj_compatible (ij : A.J × A.J) :
    A.glueData.toGlueData.diagram.fst ij ≫ TopCat.ofHom (A.localProj ij.1) =
      A.glueData.toGlueData.diagram.snd ij ≫ TopCat.ofHom (A.localProj ij.2) := by
  rcases ij with ⟨i, j⟩
  ext y
  exact (A.transition_proj i j y).symm

/-- **The glued projection.** -/
def proj : ContinuousMap A.gluedSpace X :=
  (Multicoequalizer.desc A.glueData.toGlueData.diagram (TopCat.of X) (fun i => TopCat.ofHom (A.localProj i))
    A.localProj_compatible).hom

theorem proj_incl (i : A.J) (y : A.Y i) : A.proj (A.incl i y) = (((A.T i).proj y : A.U i) : X) := by
  have h := Multicoequalizer.π_desc A.glueData.toGlueData.diagram (TopCat.of X)
    (fun i => TopCat.ofHom (A.localProj i)) A.localProj_compatible i
  exact congrArg (fun f : A.glueData.U i ⟶ TopCat.of X => f y) h

/-- The inclusions on the overlaps glue. -/
theorem incl_transition (i j : A.J) (y : A.overlap i j) :
    A.incl j (A.transition i j y : A.Y j) = A.incl i (y : A.Y i) := by
  have hc := A.glueData.toGlueData.glue_condition i j
  exact congrArg (fun f : A.glueData.V (i, j) ⟶ A.glueData.glued => f y) hc

/-- **The range of `incl i` is the saturated open `proj⁻¹ (U i)`.** -/
theorem range_incl (i : A.J) : range (A.incl i) = A.proj ⁻¹' (A.U i : Set X) := by
  ext z
  constructor
  · rintro ⟨y, rfl⟩
    change A.proj (A.incl i y) ∈ A.U i
    rw [proj_incl]
    exact ((A.T i).proj y).2
  · intro hz
    obtain ⟨j, y, rfl⟩ := A.incl_jointly_surjective z
    change A.proj (A.incl j y) ∈ A.U i at hz
    rw [proj_incl] at hz
    have hy : y ∈ A.overlap j i := A.mem_overlap.mpr hz
    exact ⟨(A.transition j i ⟨y, hy⟩ : A.Y i), A.incl_transition j i ⟨y, hy⟩⟩

theorem incl_overlap_iff (i j : A.J) (y : A.Y i) : A.incl i y ∈ range (A.incl j) ↔ y ∈ A.overlap i j := by
  rw [range_incl, mem_preimage, proj_incl, mem_overlap]
  exact Iff.rfl

/-! ### The complex manifold structure -/

theorem gluedSpace_t2 : T2Space A.gluedSpace :=
  t2Space_of_actual_saturated_projection_atlas A.proj A.proj.continuous A.U A.cover A.incl A.isOpenEmbedding_incl
    A.range_incl

theorem gluedSpace_secondCountable : SecondCountableTopology A.gluedSpace :=
  secondCountable_of_actual_saturated_projection_atlas A.proj A.U A.cover A.incl A.isOpenEmbedding_incl A.range_incl

/-- The charted space structure lifted from the local last stages. -/
@[instance_reducible]
def chartedSpace : ChartedSpace (ComplexModel n) A.gluedSpace :=
  actualLiftedTerminalChartedSpace n A.incl A.isOpenEmbedding_incl A.incl_jointly_surjective

theorem embeddingOverlap_eq (i j : A.J) :
    actualEmbeddingOverlap (A.incl i) (A.incl j) (A.isOpenEmbedding_incl i) (A.isOpenEmbedding_incl j) =
      A.overlap i j := by
  apply Opens.ext
  ext y
  exact A.incl_overlap_iff i j y

/-- The transitions between the lifted charts. -/
def embeddingTransition (i j : A.J) :
    actualEmbeddingOverlap (A.incl i) (A.incl j) (A.isOpenEmbedding_incl i) (A.isOpenEmbedding_incl j)
      ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯
    actualEmbeddingOverlap (A.incl j) (A.incl i) (A.isOpenEmbedding_incl j) (A.isOpenEmbedding_incl i) :=
  ((BlowupTowerIsoTail.opensCongr (A.embeddingOverlap_eq i j)).trans (A.transition i j)).trans
    (BlowupTowerIsoTail.opensCongr (A.embeddingOverlap_eq j i).symm)

theorem embeddingTransition_incl (i j : A.J)
    (x : actualEmbeddingOverlap (A.incl i) (A.incl j) (A.isOpenEmbedding_incl i) (A.isOpenEmbedding_incl j)) :
    A.incl j (A.embeddingTransition i j x).val = A.incl i x.val :=
  A.incl_transition i j (BlowupTowerIsoTail.opensCongr (n := n) (A.embeddingOverlap_eq i j) x)

attribute [local instance] chartedSpace

theorem isComplexManifold : IsComplexManifold n A.gluedSpace := by
  have : T2Space A.gluedSpace := A.gluedSpace_t2
  have : SecondCountableTopology A.gluedSpace := A.gluedSpace_secondCountable
  have : IsManifold 𝓘(ℂ, ComplexModel n) ∞ A.gluedSpace :=
    actualLiftedTerminalChartedSpace_isManifold A.incl A.isOpenEmbedding_incl A.incl_jointly_surjective
      A.embeddingTransition A.embeddingTransition_incl
  exact {}

attribute [local instance] isComplexManifold

/-- **The glued complex manifold.** -/
def manifold : CMfd.{u} n := CMfd.of A.gluedSpace

theorem contMDiff_incl (i : A.J) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (A.incl i : A.Y i → A.manifold) :=
  actualLiftedTerminal_local_inclusion_contMDiff A.incl A.isOpenEmbedding_incl A.incl_jointly_surjective
    A.embeddingTransition A.embeddingTransition_incl i

/-- **The glued projection is holomorphic.** -/
theorem contMDiff_proj : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (A.proj : A.manifold → X) := by
  intro z
  obtain ⟨i, x, rfl⟩ := A.incl_jointly_surjective z
  let e := chartAt (ComplexModel n) x
  let c := e.lift_openEmbedding (A.isOpenEmbedding_incl i)
  have hc : c ∈ atlas (ComplexModel n) A.manifold := ⟨i, e, chart_mem_atlas (ComplexModel n) x, rfl⟩
  have hx : x ∈ e.source := mem_chart_source (ComplexModel n) x
  have hz : A.incl i x ∈ c.source := ⟨x, hx, rfl⟩
  have heMax : e ∈ maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ (A.Y i) := chart_mem_maximalAtlas x
  have hcMax : c ∈ maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ A.manifold := subset_maximalAtlas hc
  have hlocal : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (A.localProj i) :=
    contMDiff_subtype_val.comp (A.T i).contMDiff_proj
  have hcx : c (A.incl i x) = e x := e.lift_openEmbedding_apply (A.isOpenEmbedding_incl i)
  have hsinv : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm (c (A.incl i x)) :=
    contMDiffAt_symm_of_mem_maximalAtlas heMax (by rw [hcx]; exact e.map_source hx)
  have hh := (hlocal.contMDiffAt.comp _ hsinv).comp _ (contMDiffAt_of_mem_maximalAtlas hcMax hz)
  apply hh.congr_of_eventuallyEq
  filter_upwards [c.open_source.mem_nhds hz] with y hy
  obtain ⟨b, hb, rfl⟩ := hy
  change A.proj (A.incl i b) = A.localProj i (e.symm (c (A.incl i b)))
  rw [proj_incl, e.lift_openEmbedding_apply, e.left_inv hb]
  rfl

/-! ### Properness and surjectivity -/

theorem proj_fibre (i : A.J) (x : X) (hx : x ∈ A.U i) :
    A.proj ⁻¹' ({x} : Set X) = A.incl i '' ((A.T i).proj ⁻¹' {⟨x, hx⟩}) := by
  ext z
  constructor
  · intro hz
    have hp : A.proj z = x := hz
    have hr : z ∈ range (A.incl i) := by
      rw [range_incl]
      change A.proj z ∈ A.U i
      rw [hp]
      exact hx
    obtain ⟨y, rfl⟩ := hr
    refine ⟨y, ?_, rfl⟩
    change (A.T i).proj y = ⟨x, hx⟩
    exact Subtype.ext ((A.proj_incl i y).symm.trans hp)
  · rintro ⟨y, hy, rfl⟩
    have hy' : (A.T i).proj y = ⟨x, hx⟩ := hy
    change A.proj (A.incl i y) = x
    rw [proj_incl, hy']

theorem isClosedMap_proj : IsClosedMap A.proj := by
  intro C hC
  apply isOpen_compl_iff.mp
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  obtain ⟨i, hi⟩ := A.cover x
  let Γ := A.incl i
  let u : A.U i := ⟨x, hi⟩
  let B : Set (A.Y i) := Γ ⁻¹' C
  have hB : IsClosed B := hC.preimage (A.isOpenEmbedding_incl i).continuous
  have hcl : IsClosed ((A.T i).proj '' B) := (HironakaLocalPrincipalization.isProperMap_proj (A.T i)).isClosedMap B hB
  let V : Set (A.U i) := ((A.T i).proj '' B)ᶜ
  have hV : IsOpen V := hcl.isOpen_compl
  have hu : u ∈ V := by
    rintro ⟨y, hy, hyp⟩
    apply hx
    exact ⟨Γ y, hy, (A.proj_incl i y).trans (congrArg Subtype.val hyp)⟩
  refine ⟨Subtype.val '' V, ?_, ?_, ⟨u, hu, rfl⟩⟩
  · rintro z ⟨v, hv, rfl⟩ hz
    obtain ⟨w, hw, hpw⟩ := hz
    have hr : w ∈ range Γ := by
      change w ∈ range (A.incl i)
      rw [range_incl]
      change A.proj w ∈ A.U i
      rw [hpw]
      exact v.2
    obtain ⟨y, hΓy⟩ := hr
    apply hv
    refine ⟨y, ?_, ?_⟩
    · change Γ y ∈ C
      rw [hΓy]
      exact hw
    · apply Subtype.ext
      exact (A.proj_incl i y).symm.trans ((congrArg A.proj hΓy).trans hpw)
  · exact (A.U i).isOpen.isOpenEmbedding_subtypeVal.isOpenMap V hV

/-- **The glued projection is proper.** -/
theorem isProperMap_proj : IsProperMap A.proj := by
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr ⟨A.proj.continuous, A.isClosedMap_proj, fun x => ?_⟩
  obtain ⟨i, hi⟩ := A.cover x
  rw [A.proj_fibre i x hi]
  exact ((HironakaLocalPrincipalization.isProperMap_proj (A.T i)).isCompact_preimage isCompact_singleton).image
    (A.isOpenEmbedding_incl i).continuous

/-- **The glued projection is surjective** (each blowup is). -/
theorem surjective_proj : Surjective A.proj := by
  intro x
  obtain ⟨i, hi⟩ := A.cover x
  obtain ⟨y, hy⟩ := HironakaLocalPrincipalization.IsBlowupSequence.surjective (A.T i).isBlowupSequence ⟨x, hi⟩
  exact ⟨A.incl i y, (A.proj_incl i y).trans (congrArg Subtype.val hy)⟩

/-! ### The local biholomorphisms -/

/-- The saturated open `proj⁻¹ (U i)` of the glued manifold. -/
def chartOpen (i : A.J) : Opens A.manifold :=
  ⟨A.proj ⁻¹' (A.U i : Set X), (A.U i).isOpen.preimage A.proj.continuous⟩

theorem mem_chartOpen (i : A.J) (y : A.Y i) : A.incl i y ∈ A.chartOpen i := by
  change A.incl i y ∈ A.proj ⁻¹' (A.U i : Set X)
  rw [← range_incl]
  exact ⟨y, rfl⟩

/-- The local homeomorphism onto `proj⁻¹ (U i)`. -/
def localHomeomorph (i : A.J) : A.Y i ≃ₜ A.chartOpen i :=
  ((A.isOpenEmbedding_incl i).isEmbedding.toHomeomorph).trans
    (Homeomorph.setCongr (show range (A.incl i) = (A.chartOpen i : Set A.manifold) from A.range_incl i))

theorem localHomeomorph_apply (i : A.J) (y : A.Y i) : (A.localHomeomorph i y : A.manifold) = A.incl i y := rfl

theorem localHomeomorph_symm_apply (i : A.J) (q : A.chartOpen i) :
    A.incl i ((A.localHomeomorph i).symm q) = q.val :=
  congrArg Subtype.val ((A.localHomeomorph i).apply_symm_apply q)

theorem contMDiff_localHomeomorph (i : A.J) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ (A.localHomeomorph i : A.Y i → CMfd.of (n := n) (A.chartOpen i)) :=
  BlowupRestrictOpen.contMDiff_opens_mk (V := A.chartOpen i) (A.contMDiff_incl i) (A.mem_chartOpen i)

theorem contMDiff_localHomeomorph_symm (i : A.J) :
    ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      ((A.localHomeomorph i).symm : CMfd.of (n := n) (A.chartOpen i) → A.Y i) := by
  intro q
  let H := A.localHomeomorph i
  let x := H.symm q
  let e := chartAt (ComplexModel n) x
  let c := e.lift_openEmbedding (A.isOpenEmbedding_incl i)
  have hp : A.incl i x = q.val := A.localHomeomorph_symm_apply i q
  have hc : c ∈ atlas (ComplexModel n) A.manifold := ⟨i, e, chart_mem_atlas (ComplexModel n) x, rfl⟩
  have hx : x ∈ e.source := mem_chart_source (ComplexModel n) x
  have hz : q.val ∈ c.source := ⟨x, hx, hp⟩
  have hcx : c q.val = e x := by rw [← hp]; exact e.lift_openEmbedding_apply _
  have heMax : e ∈ maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ (A.Y i) := chart_mem_maximalAtlas x
  have hcMax : c ∈ maximalAtlas 𝓘(ℂ, ComplexModel n) ∞ A.manifold := subset_maximalAtlas hc
  have hinv : ContMDiffAt 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ e.symm (c q.val) :=
    contMDiffAt_symm_of_mem_maximalAtlas heMax (by rw [hcx]; exact e.map_source hx)
  have hval : ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞
      (Subtype.val : A.chartOpen i → A.manifold) := contMDiff_subtype_val
  have hh := hinv.comp q ((contMDiffAt_of_mem_maximalAtlas hcMax hz).comp q hval.contMDiffAt)
  apply hh.congr_of_eventuallyEq
  filter_upwards [(c.open_source.preimage continuous_subtype_val).mem_nhds hz] with t ht
  obtain ⟨b, hb, hbΓ⟩ := ht
  have hpoint : H.symm t = b :=
    (A.isOpenEmbedding_incl i).injective ((A.localHomeomorph_symm_apply i t).trans hbΓ.symm)
  change H.symm t = e.symm (c t.val)
  rw [hpoint]
  change b = e.symm ((e.lift_openEmbedding (A.isOpenEmbedding_incl i)) t.val)
  rw [← hbΓ, e.lift_openEmbedding_apply, e.left_inv hb]

/-- **The last stage of `T i` is biholomorphic onto `proj⁻¹ (U i)`.** -/
def localBiholomorphism (i : A.J) :
    A.Y i ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) (A.chartOpen i) where
  toEquiv := (A.localHomeomorph i).toEquiv
  contMDiff_toFun := A.contMDiff_localHomeomorph i
  contMDiff_invFun := A.contMDiff_localHomeomorph_symm i

theorem localBiholomorphism_apply (i : A.J) (y : A.Y i) :
    (A.localBiholomorphism i y : A.manifold) = A.incl i y := rfl

theorem proj_localBiholomorphism (i : A.J) (y : A.Y i) :
    A.proj (A.localBiholomorphism i y : A.manifold) = (((A.T i).proj y : A.U i) : X) :=
  A.proj_incl i y

/-- **Gluing local towers** (packaged): a complex manifold `X'` and a holomorphic, proper, surjective `P : X' → X` such
that for every index `i` the last stage of `T i` is biholomorphic onto `P⁻¹ (U i)` over `U i`. -/
theorem exists_glued :
    ∃ (X' : CMfd.{u} n) (P : X' → X), ContMDiff 𝓘(ℂ, ComplexModel n) 𝓘(ℂ, ComplexModel n) ∞ P ∧ IsProperMap P ∧
      Surjective P ∧ ∀ i : A.J, ∃ V : Opens X', (V : Set X') = P ⁻¹' (A.U i : Set X) ∧
        ∃ φ : A.Y i ≃ₘ⟮𝓘(ℂ, ComplexModel n), 𝓘(ℂ, ComplexModel n)⟯ CMfd.of (n := n) V,
          ∀ y, P (φ y : X') = (((A.T i).proj y : A.U i) : X) :=
  ⟨A.manifold, A.proj, A.contMDiff_proj, A.isProperMap_proj, A.surjective_proj, fun i =>
    ⟨A.chartOpen i, rfl, A.localBiholomorphism i, A.proj_localBiholomorphism i⟩⟩

end TowerAtlas

end

end Hironaka.HironakaG3RTowerGluing
