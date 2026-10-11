/-
Copyright (c) 2026 Hironaka contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
import Hironaka.Analytic.SNCGlobalPrimeComponents
import Hironaka.Analytic.GlobalComponents
import Hironaka.Resolution.HironakaDivisorResidual
import Mathlib.Topology.Compactness.LocallyFinite

set_option autoImplicit false

/-!
# Genuine connected components of a possibly disconnected SNC boundary

The component family consists of actual `connectedComponentIn` sets. It is
locally finite, and compact sets select finite connected refinements. The
coordinate, support and exponent bridges use genuine geometric producers.
Blueprint: `hironaka-component-extension.tex`.
-/

open Set Filter
open scoped Topology Manifold ContDiff

namespace Hironaka.HironakaConnectedBoundaryComponents

open Hironaka.BlowupSequences NormalCrossings GlobalComponents
  RegularLocusComponent HironakaDivisorResidual
open Hironaka.HolomorphicIdealSheaves DivisorExponent

noncomputable section

variable {M : Type*} [TopologicalSpace M]

/-- The actual nonempty connected components of all original list members. -/
def boundaryComponents (E : List (Set M)) : Set (Set M) :=
  {C | ∃ i : Fin E.length, ∃ x ∈ E.get i, C = connectedComponentIn (E.get i) x}

/-- Splitting into actual connected components preserves the whole support. -/
theorem sUnion_boundaryComponents (E : List (Set M)) :
    ⋃₀ boundaryComponents E = ⋃ H ∈ E, H := by
  apply Subset.antisymm
  · rintro y ⟨C, ⟨i, x, hx, rfl⟩, hy⟩
    exact mem_iUnion₂.mpr ⟨E.get i, List.get_mem E i,
      connectedComponentIn_subset (E.get i) x hy⟩
  · intro x hx
    obtain ⟨H, hH, hxH⟩ := mem_iUnion₂.mp hx
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hH
    exact mem_sUnion.mpr ⟨connectedComponentIn (E.get i) x,
      ⟨i, x, hxH, rfl⟩, mem_connectedComponentIn hxH⟩

/-- In dimension zero the actual SNC coordinate condition forces the genuine
connected component family to be empty. -/
theorem boundaryComponents_eq_empty_of_isSNCDivisor_zero
    [ChartedSpace (ComplexModel 0) M] {E : List (Set M)}
    (hE : IsSNCDivisor 0 E) : boundaryComponents E = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  rintro C ⟨i, x, hx, -⟩
  obtain ⟨S, -, hcard, -⟩ := hE.2 x
  have hle := Finset.card_le_univ (S i)
  have hone := hcard i hx
  simp only [Fintype.card_fin] at hle
  omega

variable {m : ℕ} [ChartedSpace (ComplexModel (m + 1)) M]
  [IsComplexManifold (m + 1) M]

/-- Actual SNC geometry produces the closed connected smooth component and
its local equality with an original member. -/
theorem component_geometry {E : List (Set M)} (hE : IsSNCDivisor (m + 1) E)
    {C : Set M} (hC : C ∈ boundaryComponents E) :
    IsClosedConnectedSubmanifold (m + 1) C m ∧
      ∃ i : Fin E.length, C ⊆ E.get i ∧
        ∀ x ∈ C, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧ E.get i ∩ U = C ∩ U := by
  obtain ⟨i, x, hx, rfl⟩ := hC
  obtain ⟨V, -, hVC, -, hsub, hconn, hreg, hlocal⟩ :=
    SNCGlobalPrimeComponents.exists_global_prime_component hE i hx
  constructor
  · simpa only [hVC] using
      (show IsClosedConnectedSubmanifold (m + 1) V.carrier m from
        ⟨V.isClosed_carrier, hconn, hreg⟩)
  · simpa only [hVC] using
      (show ∃ j : Fin E.length, V.carrier ⊆ E.get j ∧
        ∀ y ∈ V.carrier, ∃ U : Set M, IsOpen U ∧ y ∈ U ∧
          E.get j ∩ U = V.carrier ∩ U from ⟨i, hsub, hlocal⟩)

omit [IsComplexManifold (m + 1) M] in
private theorem isDivNear_iff_of_eventually_mem_iff {A B : Set M} {x : M}
    {𝔞 : GermIdeal (m + 1) M} {r : ℕ}
    (h : ∀ᶠ z in 𝓝 x, z ∈ A ↔ z ∈ B) :
    IsDivNear (m + 1) 𝔞 A r x ↔ IsDivNear (m + 1) 𝔞 B r x := by
  constructor
  · intro hA
    filter_upwards [h, hA] with z hz hdiv hzB
    exact hdiv (hz.mpr hzB)
  · intro hB
    filter_upwards [h, hB] with z hz hdiv hzA
    exact hdiv (hz.mp hzA)

/-- Actual equality with the parent hypersurface near a component point
identifies their local divisibility conditions for every germ ideal. -/
theorem isDivNear_connectedComponent_iff {E : List (Set M)}
    (hE : IsSNCDivisor (m + 1) E) (i : Fin E.length) {c x : M}
    (hc : c ∈ E.get i) (hx : x ∈ connectedComponentIn (E.get i) c)
    {𝔞 : GermIdeal (m + 1) M} (r : ℕ) :
    IsDivNear (m + 1) 𝔞 (connectedComponentIn (E.get i) c) r x ↔
      IsDivNear (m + 1) 𝔞 (E.get i) r x := by
  obtain ⟨V, -, hVC, -, -, -, -, hlocal⟩ :=
    SNCGlobalPrimeComponents.exists_global_prime_component hE i hc
  obtain ⟨U, hU, hxU, heq⟩ := hlocal x (hVC.symm ▸ hx)
  rw [hVC] at heq
  apply isDivNear_iff_of_eventually_mem_iff
  filter_upwards [hU.mem_nhds hxU] with z hzU
  have hz := Set.ext_iff.mp heq z
  simpa only [mem_inter_iff, hzU, and_true] using hz.symm

/-- The totalized divisorial exponent also agrees between an actual connected
component and its original member at every point of the component. -/
theorem divExp_connectedComponent_eq {E : List (Set M)}
    (hE : IsSNCDivisor (m + 1) E) (i : Fin E.length) {c x : M}
    (hc : c ∈ E.get i) (hx : x ∈ connectedComponentIn (E.get i) c)
    (𝔞 : GermIdeal (m + 1) M) :
    divExp (m + 1) 𝔞 (connectedComponentIn (E.get i) c) x =
      divExp (m + 1) 𝔞 (E.get i) x := by
  classical
  have heq : ∀ r, IsDivNear (m + 1) 𝔞 (connectedComponentIn (E.get i) c) r x =
      IsDivNear (m + 1) 𝔞 (E.get i) r x := fun r =>
    propext (isDivNear_connectedComponent_iff hE i hc hx r)
  unfold divExp
  by_cases hC : ∃ e, ¬ IsDivNear (m + 1) 𝔞 (connectedComponentIn (E.get i) c) (e + 1) x
  · have hH : ∃ e, ¬ IsDivNear (m + 1) 𝔞 (E.get i) (e + 1) x := by
      obtain ⟨e, he⟩ := hC
      exact ⟨e, (heq (e + 1)) ▸ he⟩
    rw [dif_pos hC, dif_pos hH]
    exact Nat.find_congr' (fun {e} => not_congr
      (isDivNear_connectedComponent_iff hE i hc hx (e + 1)))
  · have hH : ¬ ∃ e, ¬ IsDivNear (m + 1) 𝔞 (E.get i) (e + 1) x := by
      rintro ⟨e, he⟩
      exact hC ⟨e, (heq (e + 1)).symm ▸ he⟩
    rw [dif_neg hC, dif_neg hH]

/-- Arbitrary values assigned to the genuine connected components glue to a
locally constant function on each possibly disconnected original member. -/
theorem isLocallyConstant_component_function {E : List (Set M)}
    (hE : IsSNCDivisor (m + 1) E) {β : Type*}
    (a : boundaryComponents E → β) (i : Fin E.length) :
    IsLocallyConstant (fun p : E.get i =>
      a ⟨connectedComponentIn (E.get i) (p : M), ⟨i, p, p.2, rfl⟩⟩) := by
  apply (IsLocallyConstant.iff_eventually_eq _).mpr
  intro p
  obtain ⟨V, -, hVC, -, -, -, -, hlocal⟩ :=
    SNCGlobalPrimeComponents.exists_global_prime_component hE i p.2
  obtain ⟨U, hU, hpU, heq⟩ := hlocal p (hVC.symm ▸ mem_connectedComponentIn p.2)
  rw [hVC] at heq
  filter_upwards [continuous_subtype_val.continuousAt.tendsto.eventually
    (hU.mem_nhds hpU)] with q hqU
  have hqC : (q : M) ∈ connectedComponentIn (E.get i) (p : M) := by
    have hq : (q : M) ∈ connectedComponentIn (E.get i) (p : M) ∩ U := by
      rw [← heq]
      exact ⟨q.2, hqU⟩
    exact hq.1
  apply congrArg a
  apply Subtype.ext
  exact (connectedComponentIn_eq hqC).symm

private theorem isAnalytic_member {E : List (Set M)}
    (hE : IsSNCDivisor (m + 1) E) (i : Fin E.length) :
    IsComplexAnalyticSubset (n := m + 1) (E.get i) :=
  AnalyticSubsetPreimage.isComplexAnalyticSubset_of_isClosedSubmanifold
    ⟨hE.1 _ (List.get_mem E i), fun _x hx =>
      ⟨m, SNCGlobalPrimeComponents.regularAtDim_member hE i hx⟩⟩

private theorem component_mem_globalComponents {E : List (Set M)}
    (hE : IsSNCDivisor (m + 1) E) (i : Fin E.length) {x : M} (hx : x ∈ E.get i) :
    connectedComponentIn (E.get i) x ∈ globalComponents (n := m + 1) (E.get i) := by
  have hRA : regularPoints (n := m + 1) (E.get i) = E.get i :=
    Subset.antisymm (regularPoints_subset _) (fun y hy =>
      ⟨m, SNCGlobalPrimeComponents.regularAtDim_member hE i hy⟩)
  have hcomp : component (n := m + 1) (E.get i) x =
      connectedComponentIn (E.get i) x := by
    unfold component
    rw [hRA]
  have hclosed : IsClosed (connectedComponentIn (E.get i) x) :=
    (component_geometry hE (show connectedComponentIn (E.get i) x ∈ boundaryComponents E
      from ⟨i, x, hx, rfl⟩)).1.1
  simpa only [hcomp, hclosed.closure_eq] using
    closure_component_mem_globalComponents (SNCGlobalPrimeComponents.regularAtDim_member hE i hx)

/-- Every ambient point has an open neighbourhood meeting only finitely many
actual connected boundary components. -/
theorem exists_isOpen_finite_boundaryComponents {E : List (Set M)}
    (hE : IsSNCDivisor (m + 1) E) (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      {C | C ∈ boundaryComponents E ∧ (C ∩ U).Nonempty}.Finite := by
  classical
  choose U hU hpU hfin using fun i : Fin E.length =>
    exists_isOpen_finite_globalComponents (isAnalytic_member hE i) p
  refine ⟨⋂ i, U i, isOpen_iInter_of_finite hU, mem_iInter.mpr hpU,
    (finite_iUnion fun i => hfin i).subset ?_⟩
  rintro C ⟨⟨i, x, hx, rfl⟩, y, hyC, hyU⟩
  exact mem_iUnion.mpr ⟨i, component_mem_globalComponents hE i hx,
    y, hyC, mem_iInter.mp hyU i⟩

/-- The genuinely nonempty component family is locally finite, even when the
ambient manifold and original smooth members are not compact. -/
theorem locallyFinite_boundaryComponents {E : List (Set M)}
    (hE : IsSNCDivisor (m + 1) E) :
    LocallyFinite (fun C : boundaryComponents E => (C : Set M)) := by
  intro p
  obtain ⟨U, hU, hpU, hfin⟩ := exists_isOpen_finite_boundaryComponents hE p
  refine ⟨U, hU.mem_nhds hpU, ?_⟩
  exact (hfin.preimage Subtype.val_injective.injOn).subset fun C hC => ⟨C.2, hC⟩

/-- Only finitely many actual boundary components meet a prescribed compact
set; no global finiteness is inferred from the original finite list. -/
theorem finite_boundaryComponents_inter_compact {E : List (Set M)}
    (hE : IsSNCDivisor (m + 1) E) {K : Set M} (hK : IsCompact K) :
    {C | C ∈ boundaryComponents E ∧ (C ∩ K).Nonempty}.Finite := by
  have hfin := (locallyFinite_boundaryComponents hE).finite_nonempty_inter_compact hK
  refine (hfin.image (Subtype.val : boundaryComponents E → Set M)).subset ?_
  rintro C ⟨hC, hCK⟩
  exact ⟨⟨C, hC⟩, hCK, rfl⟩

/-- A finite list of distinct genuine connected boundary components retains
the original simple normal crossings geometry. -/
theorem isSNCDivisor_component_refinement {E F : List (Set M)}
    (hE : IsSNCDivisor (m + 1) E) (hF : ∀ C ∈ F, C ∈ boundaryComponents E)
    (hFnodup : F.Nodup) : IsSNCDivisor (m + 1) F := by
  classical
  refine ⟨fun C hC => (component_geometry hE (hF C hC)).1.1, ?_⟩
  intro x
  have hchoice : ∀ i : Fin F.length, ∃ j : Fin E.length, ∃ c ∈ E.get j,
      F.get i = connectedComponentIn (E.get j) c :=
    fun i => hF (F.get i) (List.get_mem F i)
  choose parent point hpoint hcomponent using hchoice
  have hsub : ∀ i, F.get i ⊆ E.get (parent i) := by
    intro i
    rw [hcomponent i]
    exact connectedComponentIn_subset _ _
  have hneigh : ∀ i : Fin F.length, ∃ U : Set M, IsOpen U ∧ x ∈ U ∧
      (x ∈ F.get i → E.get (parent i) ∩ U = F.get i ∩ U) := by
    intro i
    by_cases hi : x ∈ F.get i
    · obtain ⟨V, -, hVC, -, -, -, -, hlocal⟩ :=
        SNCGlobalPrimeComponents.exists_global_prime_component hE (parent i) (hpoint i)
      have hCV : V.carrier = F.get i := hVC.trans (hcomponent i).symm
      obtain ⟨U, hU, hxU, heq⟩ := hlocal x (hCV.symm ▸ hi)
      rw [hCV] at heq
      exact ⟨U, hU, hxU, fun _ => heq⟩
    · exact ⟨univ, isOpen_univ, mem_univ x, fun h => False.elim (hi h)⟩
  choose U hU hxU heq using hneigh
  let Ω : Set M := ⋂ i, U i
  have hΩ : IsOpen Ω := isOpen_iInter_of_finite hU
  have hxΩ : x ∈ Ω := mem_iInter.mpr hxU
  obtain ⟨S, ⟨Φ, hsrc, hzero, hflat⟩, hcard, hinj⟩ := hE.2 x
  let e := (complexChartAt (n := m + 1) x).val
  have hxs : x ∈ e.source := mem_complexChartAt_source x
  let W : Set (ComplexModel (m + 1)) := e.target ∩ e.symm ⁻¹' Ω
  have hW : IsOpen W :=
    e.symm.continuousOn.isOpen_inter_preimage e.open_target hΩ
  have hxW : e x ∈ W := by
    refine ⟨e.map_source hxs, ?_⟩
    change e.symm (e x) ∈ Ω
    rw [e.left_inv hxs]
    exact hxΩ
  let Θ := Φ.restrict W hW (e x) ⟨Φ.center_mem_source, hxW⟩
  refine ⟨fun i => S (parent i), ⟨Θ, fun z hz => hsrc hz.1, hzero, ?_⟩,
    fun i hi => hcard (parent i) (hsub i hi), ?_⟩
  · intro i hi y hy hyΘ
    have hyΩ : y ∈ Ω := by
      have h : e.symm (e y) ∈ Ω := hyΘ.2.2
      simpa only [e.left_inv hy] using h
    have hyU : y ∈ U i := mem_iInter.mp hyΩ i
    have hiff : y ∈ F.get i ↔ y ∈ E.get (parent i) := by
      constructor
      · intro hyC
        have h : y ∈ E.get (parent i) ∩ U i := by
          rw [heq i hi]
          exact ⟨hyC, hyU⟩
        exact h.1
      · intro hyE
        have h : y ∈ F.get i ∩ U i := by
          rw [← heq i hi]
          exact ⟨hyE, hyU⟩
        exact h.1
    exact hiff.trans (hflat (parent i) (hsub i hi) hy hyΘ.1)
  · intro i hi j hj hij
    have hparent : parent i = parent j := hinj (hsub i hi) (hsub j hj) hij
    apply List.nodup_iff_injective_get.mp hFnodup
    have hiC : x ∈ connectedComponentIn (E.get (parent i)) (point i) := by
      rwa [← hcomponent i]
    have hjC : x ∈ connectedComponentIn (E.get (parent j)) (point j) := by
      rwa [← hcomponent j]
    calc
      F.get i = connectedComponentIn (E.get (parent i)) x :=
        (hcomponent i).trans (connectedComponentIn_eq hiC)
      _ = connectedComponentIn (E.get (parent j)) x := by rw [hparent]
      _ = F.get j := ((hcomponent j).trans (connectedComponentIn_eq hjC)).symm

private theorem isClosed_sUnion_subfamily {E : List (Set M)}
    (hE : IsSNCDivisor (m + 1) E) {T : Set (Set M)} (hT : T ⊆ boundaryComponents E) :
    IsClosed (⋃₀ T) := by
  let f : T → boundaryComponents E := fun C => ⟨C.1, hT C.2⟩
  have hf : Function.Injective f := by
    intro C D h
    exact Subtype.ext (congrArg (fun B : boundaryComponents E => (B : Set M)) h)
  have hlf := (locallyFinite_boundaryComponents hE).comp_injective hf
  have hclosed : IsClosed (⋃ C : T, (C : Set M)) := hlf.isClosed_iUnion fun C =>
    (component_geometry hE (hT C.2)).1.1
  have heq : (⋃ C : T, (C : Set M)) = ⋃₀ T := by
    ext x
    simp only [mem_iUnion, mem_sUnion]
    exact ⟨fun ⟨C, hx⟩ => ⟨C.1, C.2, hx⟩,
      fun ⟨C, hC, hx⟩ => ⟨⟨C, hC⟩, hx⟩⟩
  rwa [heq] at hclosed

/-- A compact set selects a finite SNC list of actual connected components.
The same finite list describes the boundary on an entire open neighbourhood. -/
theorem exists_finite_refinement_on_compact {E : List (Set M)}
    (hE : IsSNCDivisor (m + 1) E) {K : Set M} (hK : IsCompact K) :
    ∃ F : List (Set M), F.Nodup ∧
      (∀ C, C ∈ F ↔ C ∈ boundaryComponents E ∧ (C ∩ K).Nonempty) ∧
      IsSNCDivisor (m + 1) F ∧
      (∀ C ∈ F, IsClosedConnectedSubmanifold (m + 1) C m) ∧
      K ∩ (⋃ C ∈ F, C) = K ∩ (⋃ H ∈ E, H) ∧
      ∃ U : Set M, IsOpen U ∧ K ⊆ U ∧
        U ∩ (⋃ C ∈ F, C) = U ∩ (⋃ H ∈ E, H) := by
  classical
  let S : Set (Set M) := {C | C ∈ boundaryComponents E ∧ (C ∩ K).Nonempty}
  have hS : S.Finite := finite_boundaryComponents_inter_compact hE hK
  let F : List (Set M) := hS.toFinset.toList
  have hmem : ∀ C, C ∈ F ↔ C ∈ boundaryComponents E ∧ (C ∩ K).Nonempty := by
    intro C
    simp [F, S]
  have hF : ∀ C ∈ F, C ∈ boundaryComponents E := fun C hC => ((hmem C).mp hC).1
  have hFnodup : F.Nodup := Finset.nodup_toList _
  let T : Set (Set M) := {C | C ∈ boundaryComponents E ∧ C ∉ F}
  let U : Set M := (⋃₀ T)ᶜ
  have hU : IsOpen U := (isClosed_sUnion_subfamily hE (fun _ h => h.1)).isOpen_compl
  have hKU : K ⊆ U := by
    intro x hx hxT
    obtain ⟨C, hC, hxC⟩ := mem_sUnion.mp hxT
    exact hC.2 ((hmem C).mpr ⟨hC.1, x, hxC, hx⟩)
  have hFE : (⋃ C ∈ F, C) ⊆ ⋃ H ∈ E, H := by
    intro x hx
    obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hx
    rw [← sUnion_boundaryComponents E]
    exact mem_sUnion.mpr ⟨C, hF C hC, hxC⟩
  have hUeq : U ∩ (⋃ C ∈ F, C) = U ∩ (⋃ H ∈ E, H) := by
    apply Subset.antisymm (inter_subset_inter_right U hFE)
    rintro x ⟨hxU, hxE⟩
    rw [← sUnion_boundaryComponents E] at hxE
    obtain ⟨C, hC, hxC⟩ := mem_sUnion.mp hxE
    have hCF : C ∈ F := by
      by_contra hnot
      exact hxU (mem_sUnion.mpr ⟨C, ⟨hC, hnot⟩, hxC⟩)
    exact ⟨hxU, mem_iUnion₂.mpr ⟨C, hCF, hxC⟩⟩
  have hKeq : K ∩ (⋃ C ∈ F, C) = K ∩ (⋃ H ∈ E, H) := by
    apply Subset.antisymm (inter_subset_inter_right K hFE)
    rintro x ⟨hxK, hxE⟩
    have hxF : x ∈ U ∩ (⋃ C ∈ F, C) := by
      rw [hUeq]
      exact ⟨hKU hxK, hxE⟩
    exact ⟨hxK, hxF.2⟩
  exact ⟨F, hFnodup, hmem, isSNCDivisor_component_refinement hE hF hFnodup,
    fun C hC => (component_geometry hE (hF C hC)).1, hKeq, U, hU, hKU, hUeq⟩

/-- If the whole boundary support lies in a compact set, its actual connected
components form a global finite SNC refinement with precisely equal support. -/
theorem exists_finite_refinement_of_support_subset_isCompact {E : List (Set M)}
    (hE : IsSNCDivisor (m + 1) E) {K : Set M} (hK : IsCompact K)
    (hEK : (⋃ H ∈ E, H) ⊆ K) :
    ∃ F : List (Set M), F.Nodup ∧
      (∀ C, C ∈ F ↔ C ∈ boundaryComponents E) ∧
      IsSNCDivisor (m + 1) F ∧
      (∀ C ∈ F, IsClosedConnectedSubmanifold (m + 1) C m) ∧
      (⋃ C ∈ F, C) = ⋃ H ∈ E, H := by
  obtain ⟨F, hFnodup, hmem, hFsnc, hgeom, -, -⟩ :=
    exists_finite_refinement_on_compact hE hK
  have hmem' : ∀ C, C ∈ F ↔ C ∈ boundaryComponents E := by
    intro C
    refine ⟨fun h => ((hmem C).mp h).1, fun hC => (hmem C).mpr ⟨hC, ?_⟩⟩
    obtain ⟨x, hx⟩ := (component_geometry hE hC).1.2.1.nonempty
    refine ⟨x, hx, hEK ?_⟩
    rw [← sUnion_boundaryComponents E]
    exact mem_sUnion.mpr ⟨C, hC, hx⟩
  refine ⟨F, hFnodup, hmem', hFsnc, hgeom, ?_⟩
  rw [← sUnion_boundaryComponents E]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨C, hC, hxC⟩ := mem_iUnion₂.mp hx
    exact mem_sUnion.mpr ⟨C, (hmem' C).mp hC, hxC⟩
  · rintro x ⟨C, hC, hxC⟩
    exact mem_iUnion₂.mpr ⟨C, (hmem' C).mpr hC, hxC⟩

/-- Local constancy and genuine connected carriers produce a single function
of actual multiplicities on the whole, possibly infinite, component family. -/
theorem exists_multiplicities_boundaryComponents {E : List (Set M)}
    (hE : IsSNCDivisor (m + 1) E) (D : EffectiveDivisor (m + 1) M) :
    ∃ a : boundaryComponents E → ℕ,
      ∀ C : boundaryComponents E, ∀ x ∈ (C : Set M), ∀ r : ℕ,
        IsDivNear (m + 1) D.ideal (C : Set M) r x ↔ r ≤ a C := by
  have hcoeff : ∀ C : boundaryComponents E, ∃ a : ℕ,
      ∀ x ∈ (C : Set M), ∀ r : ℕ,
        IsDivNear (m + 1) D.ideal (C : Set M) r x ↔ r ≤ a := by
    intro C
    obtain ⟨a, R, ha, -, -, -⟩ := exists_residual_on_connected_hypersurface
      (component_geometry hE C.2).1 rfl D
    exact ⟨a, ha⟩
  choose a ha using hcoeff
  exact ⟨a, ha⟩

/-- Actual divisor multiplicities on components glue locally constantly on
the original, possibly disconnected members and characterize their local
divisibility at every point. -/
theorem exists_multiplicities_glued_boundaryComponents {E : List (Set M)}
    (hE : IsSNCDivisor (m + 1) E) (D : EffectiveDivisor (m + 1) M) :
    ∃ a : boundaryComponents E → ℕ,
      (∀ C : boundaryComponents E, ∀ x ∈ (C : Set M), ∀ r : ℕ,
        IsDivNear (m + 1) D.ideal (C : Set M) r x ↔ r ≤ a C) ∧
      ∀ i : Fin E.length,
        IsLocallyConstant (fun p : E.get i =>
          a ⟨connectedComponentIn (E.get i) (p : M), ⟨i, p, p.2, rfl⟩⟩) ∧
        ∀ p : E.get i, ∀ r : ℕ,
          IsDivNear (m + 1) D.ideal (E.get i) r (p : M) ↔
            r ≤ a ⟨connectedComponentIn (E.get i) (p : M), ⟨i, p, p.2, rfl⟩⟩ := by
  obtain ⟨a, ha⟩ := exists_multiplicities_boundaryComponents hE D
  refine ⟨a, ha, fun i => ⟨isLocallyConstant_component_function hE a i, ?_⟩⟩
  intro p r
  exact (isDivNear_connectedComponent_iff (𝔞 := D.ideal) hE i p.2
    (mem_connectedComponentIn p.2) r).symm.trans
      (ha ⟨connectedComponentIn (E.get i) (p : M), ⟨i, p, p.2, rfl⟩⟩ p
        (mem_connectedComponentIn p.2) r)

/-- A compactly supported SNC boundary, with possibly disconnected original
members, produces an actual finite connected factorization and residual. -/
theorem exists_residual_on_compact_SNC_components {E : List (Set M)}
    (hE : IsSNCDivisor (m + 1) E) {K : Set M} (hK : IsCompact K)
    (hEK : (⋃ H ∈ E, H) ⊆ K) (D : EffectiveDivisor (m + 1) M) :
    ∃ F : List (Set M), F.Nodup ∧
      (∀ C, C ∈ F ↔ C ∈ boundaryComponents E) ∧ IsSNCDivisor (m + 1) F ∧
      (⋃ C ∈ F, C) = ⋃ H ∈ E, H ∧
      ∃ A : List (Set M × ℕ), A.map Prod.fst = F ∧
        ∃ R : EffectiveDivisor (m + 1) M,
          D.ideal = (componentPowerProduct (n := m + 1) A).mul R.ideal ∧
          (∀ C ∈ F, ¬ C ⊆ R.support) ∧ R.support ⊆ D.support := by
  obtain ⟨F, hFnodup, hmem, hFsnc, hgeom, hsupport⟩ :=
    exists_finite_refinement_of_support_subset_isCompact hE hK hEK
  obtain ⟨A, hAF, R, hD, hnot, hsub⟩ :=
    exists_residual_on_finite_connected_hypersurfaces F
      (fun C hC => ⟨m, hgeom C hC, rfl⟩) D
  exact ⟨F, hFnodup, hmem, hFsnc, hsupport, A, hAF, R, hD, hnot, hsub⟩

end

end Hironaka.HironakaConnectedBoundaryComponents
