import Hironaka.Analytic.Unibranch.HironakaG10RdDbetaStep
import Hironaka.Analytic.Unibranch.HironakaG10RdMacroStep
import Hironaka.Analytic.Unibranch.HironakaG10RdStratification
import Hironaka.Analytic.Unibranch.HironakaG10MwStepProperImage
import Hironaka.Analytic.Unibranch.HironakaG10EpZeroLocus
import Hironaka.Analytic.Unibranch.HironakaG10SbTransportClosed
import Hironaka.Analytic.Unibranch.HironakaG10TmFlattenerCover
import Hironaka.Analytic.Unibranch.HironakaG10LocalSupportAnalytic

/-!
# Lemma 4.5.5 and the `D_β` step of Theorem `I_n` (lane G10RD)

Plan item L4 (`hDβ` of `HironakaG10RdMacroStep`), the half `i > 0`.  Source: H. Hironaka, *Flattening theorem in
complex-analytic geometry*, Amer. J. Math. 97 (1975), Lemma 4.5.5, printed p. 543: "Then `Δ'` consists of some of the
strict transforms of `s_kc ∈ Δ` with `k < i` (and nothing else)."  We prove the part used on p. 544 ("(4.5.5) implies
that the assumption of (4.5.1) is satisfied by an integer smaller than `i`"):

* `eventually_transportedSupport_iff` — near a point lying over a common support point of two local flatteners, their
  transported supports coincide (Hironaka: "`Z` locally coincides with `Z_r` … at every point where the two meet");
* `isAnalyticSubset_inter_of_relClosed` — a closed analytic set inside an open `W` cuts a set which is locally
  analytic on its domain and relatively closed in `W` in a global analytic set;
* `isRelOpen_transport_of_subset_aux` — the case `s'_kc ⊆ π⁻¹(D_β)` of the proof: the strict transform `Z''` of the
  auxiliary flattener contains `s'_kc` entirely (identity principle), hence every `s'_kc ∩ Z_r*` is open in `s'_kc`;
* **`badComponents_next_lt`** — Lemma 4.5.5: after the `D_β` step at index `t` every bad component of the new datum
  has index `< t`;
* **`exists_Dβ_step_of_frisch`** — the full `D_β` step of the macro-step (`t = 0`: open tracked supports; `t > 0`:
  the index drops), from Frisch's two theorems (`hF1`, `hF2`, as in `HironakaG10RdStratification`) and Lemma 4.4.5
  for sum centres (`hT`, lane G10SB, applied to every local flattener);
* **`hDβ_of_frisch`** — the same in exactly the shape of the hypothesis `hDβ` of `HironakaG10RdMacroStep`.

No named input is introduced.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter TopologicalSpace CategoryTheory AlgebraicGeometry
open scoped Topology
open Hironaka

namespace Hironaka.Analytic.Unibranch.HironakaG10RdLemma455

open Hironaka HironakaSingularModuleSheafStalk
open Hironaka.Analytic.Unibranch.SourceReducedComplexSpace
  Hironaka.Analytic.Unibranch.HironakaG10HirLocalFlattener
  Hironaka.Analytic.Unibranch.HironakaG10HirGermFlattener
  Hironaka.Analytic.Unibranch.HironakaG10LocallyAnalyticTrace
  Hironaka.Analytic.Unibranch.HironakaG10NativeAnalyticClosureDifference
  Hironaka.Analytic.Unibranch.HironakaG10LocalSupportAnalytic
  Hironaka.Analytic.Unibranch.HironakaG10RelativeNonflatStrata
  Hironaka.Analytic.Unibranch.HironakaG10SourceCSet
  Hironaka.Analytic.Unibranch.HironakaG10StratumComponentFiniteness
  Hironaka.Analytic.Unibranch.HironakaG10ChowTrackedDatum
  Hironaka.Analytic.Unibranch.HironakaG10ChowFlatteningDriver
  Hironaka.Analytic.Unibranch.HironakaG10ChowCentreMachine
  Hironaka.Analytic.Unibranch.HironakaG10ChowStrictFlatLocus
  Hironaka.Analytic.Unibranch.HironakaG10TmStratumBoundaryAt
  Hironaka.Analytic.Unibranch.HironakaG10TmFlattenerCover
  Hironaka.Analytic.Unibranch.HironakaG10MwStrataStep
  Hironaka.Analytic.Unibranch.HironakaG10MwStepProperImage
  Hironaka.Analytic.Unibranch.HironakaG10EpZeroLocus
  Hironaka.Analytic.Unibranch.HironakaG10SbFlattenerSupportGerm
  Hironaka.Analytic.Unibranch.HironakaG10SbTransportClosed
  Hironaka.Analytic.Unibranch.HironakaG10RdPermRun
  Hironaka.Analytic.Unibranch.HironakaG10RdTopIndex
  Hironaka.Analytic.Unibranch.HironakaG10RdLemma454
  Hironaka.Analytic.Unibranch.HironakaG10RdDbetaStep
  Hironaka.Analytic.Unibranch.HironakaG10RdStratification
  Hironaka.Analytic.Unibranch.HironakaG10RdMacroStep
  Hironaka.Analytic.Unibranch.EmbeddedIdealBlowupNonunitLocus

noncomputable section

/-! ### Generalities -/

/-- Relative openness passes to subsets. -/
theorem isRelOpen_of_subset {α : Type*} [TopologicalSpace α] {A A' T : Set α} (h : IsRelOpen A T)
    (hA : A' ⊆ A) : IsRelOpen A' T := by
  obtain ⟨U, hU, hAU⟩ := h
  refine ⟨U, hU, ?_⟩
  calc A' ∩ T = A' ∩ (A ∩ T) := by rw [← inter_assoc, inter_eq_left.mpr hA]
    _ = A' ∩ (A ∩ U) := by rw [hAU]
    _ = A' ∩ U := by rw [← inter_assoc, inter_eq_left.mpr hA]

/-- The support of a local flattener is locally analytic on its domain. -/
theorem isLocallyAnalyticOn_support {X Y : SourceReducedComplexSpace} {f : Y ⟶ X}
    (Z : LocalFlattener f) : IsLocallyAnalyticOn X Z.V Z.support := fun x hx => by
  obtain ⟨e, he, -, A, hA, h⟩ := local_support_analytic Z x hx
  exact ⟨e, he, A, hA, h⟩

/-- **A closed analytic set inside an open `W` cuts a relatively closed, locally analytic set in a global analytic
set.** -/
theorem isAnalyticSubset_inter_of_relClosed {X : SourceReducedComplexSpace} {C T V W : Set X.obj.left}
    (hC : X.IsAnalyticSubset C) (hCc : IsClosed C) (hV : IsOpen V) (hT : IsLocallyAnalyticOn X V T)
    (hTV : T ⊆ V) (hW : IsOpen (W \ T)) (hCW : C ⊆ W) : X.IsAnalyticSubset (C ∩ T) := by
  intro x
  by_cases hxT : x ∈ T
  · obtain ⟨e, he, heV, -⟩ := LocalEmbedding.exists_domain x hV (hTV hxT)
    refine ⟨e, he, (Subtype.val '' (e.toPoint ⁻¹' C)) ∩ (Subtype.val '' (e.toPoint ⁻¹' T)),
      (analytic_image_trace hC e).inter (analytic_image_local_trace hT e heV), ?_⟩
    rw [Set.preimage_inter, Set.preimage_inter, Set.preimage_image_eq _ Subtype.val_injective,
      Set.preimage_image_eq _ Subtype.val_injective]
  · have hO : IsOpen ((W \ T) ∪ Cᶜ) := hW.union hCc.isOpen_compl
    have hxO : x ∈ (W \ T) ∪ Cᶜ := by
      by_cases hxC : x ∈ C
      · exact Or.inl ⟨hCW hxC, hxT⟩
      · exact Or.inr hxC
    obtain ⟨e, he, heO, -⟩ := LocalEmbedding.exists_domain x hO hxO
    refine ⟨e, he, ∅, isComplexAnalyticSubset_empty, ?_⟩
    ext y
    simp only [mem_preimage, mem_inter_iff, mem_empty_iff_false, iff_false]
    rintro ⟨hyC, hyT⟩
    rcases heO ⟨y, rfl⟩ with h | h
    · exact h.2 hyT
    · exact h hyC

/-! ### Transported supports near common support points -/

/-- **Near a point over a common support point of two local flatteners, their transported supports coincide**
(Hironaka p. 543: "`Z` locally coincides with `Z_r` … at every point where the two meet"). -/
theorem eventually_transportedSupport_iff (s : Stage) (c : AdmissibleCentre s.f)
    (Z₁ Z₂ : LocalFlattener s.f) {x' : (nextWith s c).X.obj.left}
    (h₁ : (stepσ s c).hom.left.base x' ∈ Z₁.support) (h₂ : (stepσ s c).hom.left.base x' ∈ Z₂.support) :
    ∀ᶠ y' in 𝓝 x', y' ∈ transportedSupport s c Z₁ ↔ y' ∈ transportedSupport s c Z₂ := by
  have hN : ∀ᶠ y in 𝓝 ((stepσ s c).hom.left.base x'), y ∈ Z₁.V ∧ y ∈ Z₂.V ∧ Z₁.H y = Z₂.H y := by
    filter_upwards [Z₁.isOpen.mem_nhds h₁.1, Z₂.isOpen.mem_nhds h₂.1, Z₁.eventually_eq Z₂ h₁ h₂]
      with z hz1 hz2 hz3
    exact ⟨hz1, hz2, hz3⟩
  filter_upwards [((stepσ s c).hom.left.base.hom.continuous.continuousAt (x := x')).eventually hN]
    with y' hy'
  obtain ⟨hy1, hy2, hyH⟩ := hy'
  constructor
  · rintro ⟨⟨-, hH⟩, hst⟩
    refine ⟨⟨hy2, ?_⟩, hst⟩
    rw [← hyH]
    exact hH
  · rintro ⟨⟨-, hH⟩, hst⟩
    refine ⟨⟨hy1, ?_⟩, hst⟩
    rw [hyH]
    exact hH

/-- **The exceptional case of Lemma 4.5.5** (p. 543, "Let us next consider the case in which `s'_kc ⊆ π⁻¹(D_β)`"):
if an irreducible analytic `C'` lies over the support of the auxiliary flattener `Zaux`, the transported support of
some `Z₀` contains a neighbourhood of one of its points in `C'`, and `Zaux` transports to a local flattener `Z''`,
then `C'` meets every transported support relatively openly. -/
theorem isRelOpen_transport_of_subset_aux (s : Stage) (c : AdmissibleCentre s.f) (Zaux : LocalFlattener s.f)
    (Z'' : LocalFlattener (nextWith s c).f) (hZ'' : Z''.support = transportedSupport s c Zaux)
    {C' : Set (nextWith s c).X.obj.left} (hC' : (nextWith s c).X.IsIrreducibleAnalyticSubset C')
    (hCaux : C' ⊆ (stepσ s c).hom.left.base ⁻¹' Zaux.support)
    (Z₀ : LocalFlattener s.f) {x₀ : (nextWith s c).X.obj.left} (hx₀C : x₀ ∈ C')
    (hx₀ : x₀ ∈ transportedSupport s c Z₀)
    (hloc : ∀ᶠ y in 𝓝 x₀, y ∈ C' → y ∈ transportedSupport s c Z₀)
    (Z : LocalFlattener s.f) : IsRelOpen C' (transportedSupport s c Z) := by
  -- the strict transform `Z''` of `Zaux` contains `C'` entirely
  have hA : (nextWith s c).X.IsAnalyticSubset (C' ∩ Z''.support) := by
    refine isAnalyticSubset_inter_of_relClosed (W := (stepσ s c).hom.left.base ⁻¹' Zaux.V) hC'.1
      hC'.1.isClosed Z''.isOpen (isLocallyAnalyticOn_support Z'') (fun _ h => h.1) ?_ ?_
    · rw [hZ'']
      exact isOpen_preimage_diff_transportedSupport s c Zaux
    · exact fun y hy => (hCaux hy).1
  have hev := eventually_transportedSupport_iff s c Z₀ Zaux hx₀.1 (hCaux hx₀C)
  have hN : ∀ᶠ y in 𝓝 x₀, (y ∈ C' → y ∈ transportedSupport s c Z₀) ∧
      (y ∈ transportedSupport s c Z₀ ↔ y ∈ transportedSupport s c Zaux) := hloc.and hev
  obtain ⟨v, hv, hvsub⟩ := hN.exists_mem
  have hsubZ : C' ⊆ Z''.support := by
    have heq : C' ∩ Z''.support = C' := by
      refine eq_of_subset_of_inter_open_subset hA hC' inter_subset_left isOpen_interior
        ⟨x₀, hx₀C, mem_interior_iff_mem_nhds.mpr hv⟩ ?_
      intro y hy
      obtain ⟨hy1, hy2⟩ := hvsub y (interior_subset hy.2)
      refine ⟨hy.1, ?_⟩
      rw [hZ'']
      exact hy2.mp (hy1 hy.1)
    intro y hy
    rw [← heq] at hy
    exact hy.2
  -- every transported support meets `C'` relatively openly
  refine isRelOpen_of_local fun y hy => ?_
  obtain ⟨w, hw, hwsub⟩ := (eventually_transportedSupport_iff s c Z Zaux hy.2.1 (hCaux hy.1)).exists_mem
  refine ⟨interior w, isOpen_interior, mem_interior_iff_mem_nhds.mpr hw, fun z hz => ?_⟩
  have hzZ'' := hsubZ hz.1
  rw [hZ''] at hzZ''
  exact (hwsub z (interior_subset hz.2)).mpr hzZ''

/-! ### Lemma 4.5.5 -/

variable {s : Stage} {q : ℕ}

/-- The supports of the next datum of a permissible step are the transported supports. -/
theorem permStep_support_eq {R : FDatum s q} (st : PermStep R) (p : Fin q) :
    (st.next.Z p).support = transportedSupport s st.c (R.Z p) :=
  (st.next_support p).trans (by ext x'; rfl)

/-- **Lemma 4.5.5** (Hironaka p. 543), in the form used on p. 544: after a permissible step `st` (a) after which the
strict transform of the stratum `s_t` meets every transported support relatively openly (Lemma 4.5.4) and (b) whose
centre lies in the support of a local flattener `Zaux` whose transport is a local flattener `Z''`, every bad component
of the new datum has index `< t`. -/
theorem badComponents_next_lt (hf : IsProperMap s.f.hom.left.base) {R : FDatum s q} (st : PermStep R)
    (t : ℕ) (Zaux : LocalFlattener s.f)
    (hopen : ∀ p, IsRelOpen (strictSet s st.c (strata s.f R.B t)) (st.next.Z p).support)
    (hDaux : nonunitLocus st.c.B st.c.b ⊆ Zaux.support)
    (Z'' : LocalFlattener (nextWith s st.c).f) (hZ'' : Z''.support = transportedSupport s st.c Zaux) :
    ∀ jC ∈ badComponents (nextWith s st.c).f st.next.B (fun p => (st.next.Z p).support), jC.1 < t := by
  have hDa : s.X.IsAnalyticSubset (nonunitLocus st.c.B st.c.b) := by
    have := st.c.finiteType
    exact isAnalyticSubset_nonunitLocus st.c.B st.c.b
  rintro ⟨k, C'⟩ ⟨-, hcomp, ⟨p, x₀, ⟨hx₀C, hx₀s⟩, hx₀Z⟩, r, hr⟩
  change IsStratumComponent (nextWith s st.c).f st.next.B k C' at hcomp
  change x₀ ∈ C' at hx₀C
  change x₀ ∉ strata (nextWith s st.c).f st.next.B (k + 1) at hx₀s
  change x₀ ∈ (st.next.Z p).support at hx₀Z
  change ¬ IsRelOpen C' (st.next.Z r).support at hr
  change k < t
  by_contra hkt'
  have hkt : t ≤ k := not_lt.mp hkt'
  apply hr
  by_cases hCE : C' ⊆ σb s st.c ⁻¹' nonunitLocus st.c.B st.c.b
  · -- the exceptional case: `C' ⊆ π⁻¹(D_β)`
    have hflat : FlatOverAt (nextWith s st.c).f x₀
        (vanishingIdealAt (nextWith s st.c).X.obj.left
          (strata (nextWith s st.c).f st.next.B k) x₀) := by
      by_contra h
      exact hx₀s ⟨hcomp.2.1 hx₀C, h⟩
    have hloc : ∀ᶠ y in 𝓝 x₀, y ∈ C' → y ∈ (st.next.Z p).support := by
      filter_upwards [eventually_mem_support_of_flat (st.next.Z p) hx₀Z hflat] with y hy hyC
      exact ⟨hy.1, ne_top_of_le_vanishingIdealAt (hcomp.2.1 hyC) hy.2⟩
    rw [permStep_support_eq st] at hx₀Z hloc ⊢
    exact isRelOpen_transport_of_subset_aux s st.c Zaux Z'' hZ'' hcomp.1
      (fun y hy => hDaux (hCE hy)) (R.Z p) hx₀C hx₀Z hloc (R.Z r)
  · -- the strict-transform case: `C'` is the strict transform of a component of `s_k ⊆ s_t`
    rw [st.next_B] at hcomp
    obtain ⟨C, hC, -, rfl⟩ :=
      exists_isStratumComponent_of_next_proper s st.c hf R.closed hDa k hcomp hCE
    exact isRelOpen_of_subset (hopen r)
      (strictSet_mono s st.c (hC.2.1.trans (strata_antitone hkt)))

/-- If every bad component has index `< t` with `t > 0`, Hironaka's index is `< t`. -/
theorem topIndexOf_lt {s' : Stage} (R' : FDatum s' q) {t : ℕ} (ht : 0 < t)
    (h : ∀ jC ∈ badComponents s'.f R'.B (fun p => (R'.Z p).support), jC.1 < t) :
    topIndexOf R' < t := by
  unfold topIndexOf
  split_ifs with hb
  · have := topIndex_le hb (i := t - 1) fun jC hjC => by have := h jC hjC; omega
    omega
  · exact ht

/-- Hironaka's index of a datum is `topIndex` once a bound exists. -/
theorem topIndexOf_eq {s' : Stage} (R' : FDatum s' q)
    (hb : ∃ i, ∀ jC ∈ badComponents s'.f R'.B (fun p => (R'.Z p).support), jC.1 ≤ i) :
    topIndexOf R' = topIndex s'.f R'.B (fun p => (R'.Z p).support) hb := by
  unfold topIndexOf
  rw [dif_pos hb]

/-! ### The `D_β` step -/

/-- **`C_i` is analytic and closed** (Lemma 4.5.1), from Frisch's theorems. -/
theorem csetOf_analytic_closed [CompactSpace s.X.obj.left] (R : FDatum s q)
    (hF1 : ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → s.X.IsAnalyticSubset (relNonflat s.f A))
    (hF2 : ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat s.f A))
    (hB : s.X.IsAnalyticSubset R.B) :
    s.X.IsAnalyticSubset (csetOf R) ∧ IsClosed (csetOf R) := by
  have hA := strata_analytic s.f hF1 hB
  have hpr := strata_succ_ne s.f hF1 hF2 hB
  have hbd : ∃ i, ∀ jC ∈ badComponents s.f R.B (fun p => (R.Z p).support), jC.1 ≤ i :=
    exists_topIndex_bound hA hpr
  obtain ⟨h1, h2, -⟩ := lemma_4_5_1_at_topIndex R.Z hA hpr hbd
  unfold csetOf
  rw [topIndexOf_eq R hbd]
  exact ⟨h1, h2⟩

/-- **The `D_β` step of the macro-step** (Hironaka pp. 541–544): over a compact base, for a proper family flat over
`C_i`, one permissible step after which, if `i = 0`, every tracked support is relatively open in the new `B`, and, if
`i > 0`, Hironaka's index drops (Lemma 4.5.5).  Inputs: Frisch's theorems on this stage (`hF1`, `hF2`) and Lemma 4.4.5
for sum centres (`hT`) for every local flattener. -/
theorem exists_Dβ_step_of_frisch [CompactSpace s.X.obj.left] (hf : IsProperMap s.f.hom.left.base)
    (R : FDatum s q)
    (hF1 : ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → s.X.IsAnalyticSubset (relNonflat s.f A))
    (hF2 : ∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat s.f A))
    (hT : ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
      (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
      ∀ Z : LocalFlattener s.f, ∃ Z' : LocalFlattener (nextWith s c).f,
        Z'.support = transportedSupport s c Z)
    (hB : s.X.IsAnalyticSubset R.B) (hflatC : relNonflat s.f (csetOf R) = ∅) :
    ∃ st : PermStep R, (topIndexOf R = 0 → OpenTracked st.next) ∧
      (0 < topIndexOf R → topIndexOf st.next < topIndexOf R) := by
  have hA := strata_analytic s.f hF1 hB
  have hpr := strata_succ_ne s.f hF1 hF2 hB
  obtain ⟨N, -, hN, hcov, hfin, -, -⟩ :=
    exists_finite_depth_component_data s.f R.B (fun p => (R.Z p).support) hA hpr
  have hbd : ∃ i, ∀ jC ∈ badComponents s.f R.B (fun p => (R.Z p).support), jC.1 ≤ i :=
    exists_topIndex_bound hA hpr
  have hmax : ∀ jC ∈ badComponents s.f R.B (fun p => (R.Z p).support), jC.1 ≤ topIndexOf R := by
    rw [topIndexOf_eq R hbd]
    exact le_topIndex hbd
  -- the auxiliary flattener `Z ⊇ C_i` of Lemma 4.5.2 (Hironaka Th. 2.4, lane G10TM's P3′)
  obtain ⟨-, hCc⟩ := csetOf_analytic_closed R hF1 hF2 hB
  obtain ⟨Zaux, -, hZaux⟩ := exists_localFlattener_of_isClosed s.f hf univ isOpen_univ _ hCc
    fun x hx => by
      by_contra h
      have hx' : x ∈ relNonflat s.f (csetOf R) := ⟨hx.1, h⟩
      rw [hflatC] at hx'
      exact hx'
  have hC : Cset s.f R.B (fun p => (R.Z p).support) (topIndexOf R) ⊆ Zaux.support :=
    fun x hx => hZaux ⟨hx, mem_univ x⟩
  have hTR : ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
      (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
      ∃ Z' : Fin q → LocalFlattener (nextWith s c).f,
        ∀ p, (Z' p).support = (R.trackedTransport c).Z p := fun c β h1 h2 =>
    ⟨fun p => (hT c β h1 h2 (R.Z p)).choose,
      fun p => (hT c β h1 h2 (R.Z p)).choose_spec.trans (by ext x'; rfl)⟩
  obtain ⟨st, ⟨β, -, hsum⟩, hcQ, hopen⟩ := exists_Dβ_permStep R Zaux (topIndexOf R)
    (fun _ => locallyAnalytic_of_analytic (hA _) _) (locallyAnalytic_of_analytic (hA _) _)
    (isClosed_strata_of_proper s.f hf R.closed _) N hN hcov (hfin _) hmax hC
    (dense_compl_nonflatImage s.f hF2) hTR
  refine ⟨st, fun h0 p => ?_, fun hpos => ?_⟩
  · have h := hopen p
    rw [h0] at h
    rw [st.next_B]
    exact h
  · obtain ⟨Z'', hZ''⟩ := hT st.c β hsum st.flat Zaux
    have hDaux : nonunitLocus st.c.B st.c.b ⊆ Zaux.support := by
      rw [hcQ]
      exact fun x hx => hx.2.2
    exact topIndexOf_lt st.next hpos (badComponents_next_lt hf st _ Zaux hopen hDaux Z'' hZ'')

/-- **`hDβ` of `HironakaG10RdMacroStep`** for any dimension predicate implying analyticity, from Frisch's theorems on
every compact stage with a proper family (`hFrisch`, the form of lane G10TM's `HironakaG10TmFlattenerCover`) and
Lemma 4.4.5 for sum centres on every such stage (`hT`). -/
theorem hDβ_of_frisch (dim : ℕ → ∀ s : Stage, Set s.X.obj.left → Prop)
    (hdimA : ∀ (n : ℕ) (s : Stage) (B : Set s.X.obj.left), dim n s B → s.X.IsAnalyticSubset B)
    (hFrisch : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      (∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → s.X.IsAnalyticSubset (relNonflat s.f A)) ∧
      (∀ A : Set s.X.obj.left, s.X.IsAnalyticSubset A → A ⊆ closure (A \ relNonflat s.f A)))
    (hT : ∀ s : Stage, CompactSpace s.X.obj.left → IsProperMap s.f.hom.left.base →
      ∀ (c : AdmissibleCentre s.f) (β : ℕ), IsSumCentreFor c.B c.b s.f β →
        (∀ x ∈ nonunitLocus c.B c.b, FlatOverAt s.f x (centreIdeal c x)) →
        ∀ Z : LocalFlattener s.f, ∃ Z' : LocalFlattener (nextWith s c).f,
          Z'.support = transportedSupport s c Z) :
    ∀ (n : ℕ) (s : Stage) (q : ℕ) (R : FDatum s q), CompactSpace s.X.obj.left →
      IsProperMap s.f.hom.left.base → dim (n + 1) s R.B → relNonflat s.f (csetOf R) = ∅ →
        ∃ st : PermStep R, (topIndexOf R = 0 → OpenTracked st.next) ∧
          (0 < topIndexOf R → topIndexOf st.next < topIndexOf R) :=
  fun _ s _ R hc hp hd hflatC =>
    exists_Dβ_step_of_frisch hp R (hFrisch s hc hp).1 (hFrisch s hc hp).2 (hT s hc hp)
      (hdimA _ s _ hd) hflatC

end

end Hironaka.Analytic.Unibranch.HironakaG10RdLemma455
