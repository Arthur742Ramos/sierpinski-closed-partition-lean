/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module

public import Mathlib.Topology.Separation.Regular

/-!
# Sierpiński's closed-partition theorem

A countable closed partition of a nonempty compact connected Hausdorff
space has a piece equal to the whole space. The continuous-choice corollary
uses this theorem on closed equalizers.

The Boundary Bumping section below is reused under Apache 2.0 from
Arthur742Ramos/boundary-bumping-lean, commit
58831416a12f73312ac01cdaec19c060a6d4b142. See PROVENANCE.md.
-/

@[expose] public section

open Set

namespace BoundaryBumping

variable {X : Type*} [TopologicalSpace X]

/-- An open neighborhood of a component in a compact Hausdorff space contains
a clopen neighborhood of the whole component. -/
theorem exists_clopen_between_component_and_open [CompactSpace X] [T2Space X]
    (x : X) {U : Set X} (hU : IsOpen U) (hCU : connectedComponent x ⊆ U) :
    ∃ V : Set X, IsClopen V ∧ connectedComponent x ⊆ V ∧ V ⊆ U := by
  classical
  let N := {s : Set X // IsClopen s ∧ x ∈ s}
  have hdisj : Disjoint Uᶜ (⋂ s : N, (s : Set X)) := by
    rw [← connectedComponent_eq_iInter_isClopen x]
    exact disjoint_compl_left_iff_subset.mpr hCU
  obtain ⟨a, ha⟩ := hU.isClosed_compl.isCompact.elim_finite_subfamily_closed
    (fun s : N => (s : Set X)) (fun s => s.2.1.1) hdisj
  let V : Set X := ⋂ s ∈ a, (s : Set X)
  have hV : IsClopen V := isClopen_biInter_finset fun s _ => s.2.1
  have hxV : x ∈ V := mem_iInter₂.mpr fun s _ => s.2.2
  exact ⟨V, hV, hV.connectedComponent_subset hxV,
    disjoint_compl_left_iff_subset.mp ha⟩

/-- A relatively clopen subset of a closed set, contained in its interior,
has clopen image in the ambient space. -/
private theorem clopen_image_of_subset_interior {F : Set X} (hF : IsClosed F)
    {V : Set F} (hV : IsClopen V)
    (hVF : Subtype.val '' V ⊆ interior F) : IsClopen (Subtype.val '' V) := by
  refine ⟨hF.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed.mp hV.1, ?_⟩
  obtain ⟨O, hO, hpre⟩ := isOpen_induced_iff.mp hV.2
  have hOV : Subtype.val '' V = O ∩ F := by
    rw [← hpre, Subtype.image_preimage_coe, inter_comm]
  have hEq : Subtype.val '' V = O ∩ interior F := by
    apply Subset.antisymm
    · intro y hy
      exact ⟨(hOV ▸ hy).1, hVF hy⟩
    · intro y hy
      rw [hOV]
      exact ⟨hy.1, interior_subset hy.2⟩
  rw [hEq]
  exact hO.inter isOpen_interior

/-- **Boundary Bumping Theorem**, closed-subset version: every component of a
proper closed subset of a compact connected Hausdorff space meets its frontier. -/
theorem closed_component_meets_frontier [CompactSpace X] [T2Space X] [ConnectedSpace X]
    {F : Set X} (hF : IsClosed F) (hproper : F ≠ univ) {x : X} (hx : x ∈ F) :
    (connectedComponentIn F x ∩ frontier F).Nonempty := by
  classical
  by_contra hmiss
  have hCI : connectedComponentIn F x ⊆ interior F := by
    intro y hy
    by_contra hyI
    apply hmiss
    exact ⟨y, hy, by
      rw [frontier, hF.closure_eq]
      exact ⟨connectedComponentIn_subset F x hy, hyI⟩⟩
  have : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  let p : F := ⟨x, hx⟩
  obtain ⟨V, hV, hCV, hVI⟩ := exists_clopen_between_component_and_open p
    (isOpen_interior.preimage continuous_subtype_val) (by
      intro y hy
      exact hCI (by rw [connectedComponentIn_eq_image hx]; exact ⟨y, hy, rfl⟩))
  have hImage : IsClopen (Subtype.val '' V : Set X) :=
    clopen_image_of_subset_interior hF hV (by
      rintro _ ⟨y, hy, rfl⟩
      exact hVI hy)
  have hxImage : x ∈ (Subtype.val '' V : Set X) :=
    ⟨p, hCV mem_connectedComponent, rfl⟩
  apply hproper
  apply Subset.antisymm (subset_univ F)
  intro y _
  have hy : y ∈ (Subtype.val '' V : Set X) := by
    rw [hImage.eq_univ ⟨x, hxImage⟩]
    trivial
  rcases hy with ⟨z, _, rfl⟩
  exact z.2

/-- A proper closed subset of a continuum contains, through each of its points,
a compact connected subset that meets the frontier of the closed subset. -/
theorem exists_subcontinuum_meeting_frontier [CompactSpace X] [T2Space X] [ConnectedSpace X]
    {F : Set X} (hF : IsClosed F) (hproper : F ≠ univ) {x : X} (hx : x ∈ F) :
    ∃ K : Set X, IsCompact K ∧ IsConnected K ∧ x ∈ K ∧ K ⊆ F ∧
      (K ∩ frontier F).Nonempty := by
  have : CompactSpace F := isCompact_iff_compactSpace.mp hF.isCompact
  refine ⟨connectedComponentIn F x, ?_, isConnected_connectedComponentIn_iff.mpr hx,
    mem_connectedComponentIn hx, connectedComponentIn_subset F x,
    closed_component_meets_frontier hF hproper hx⟩
  rw [connectedComponentIn_eq_image hx]
  exact isClosed_connectedComponent.isCompact.image continuous_subtype_val

end BoundaryBumping

universe u v w

namespace Sierpinski

variable {X : Type u} [tX : TopologicalSpace X] [t2X : T2Space X]

/- This shrinking statement is used only in the contradiction argument.
   Its hypotheses will eventually be shown inconsistent. -/
private theorem shrink_continuum (F : ℕ → Set X)
    (hclosed : ∀ n, IsClosed (F n))
    (hdisjoint : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hcover : ⋃ n, F n = univ)
    {C : Set X} (hcompact : IsCompact C) (hconnected : IsConnected C)
    (htwo : ∃ i j, i ≠ j ∧ (C ∩ F i).Nonempty ∧ (C ∩ F j).Nonempty)
    (n : ℕ) :
    ∃ D : Set X, IsCompact D ∧ IsConnected D ∧ D ⊆ C ∧
      Disjoint D (F n) ∧
      ∃ i j, i ≠ j ∧ (D ∩ F i).Nonempty ∧ (D ∩ F j).Nonempty := by
  classical
  by_cases hmiss : Disjoint C (F n)
  · exact ⟨C, hcompact, hconnected, subset_rfl, hmiss, htwo⟩
  let : CompactSpace C := isCompact_iff_compactSpace.mp hcompact
  let : ConnectedSpace C := Subtype.connectedSpace hconnected
  let G : ℕ → Set C := fun k => Subtype.val ⁻¹' F k
  have hGclosed (k : ℕ) : IsClosed (G k) :=
    (hclosed k).preimage continuous_subtype_val
  obtain ⟨i, j, hij, hi, hj⟩ := htwo
  have hm : ∃ m, m ≠ n ∧ (C ∩ F m).Nonempty := by
    by_cases hin : i = n
    · exact ⟨j, fun hjn => hij (hin.trans hjn.symm), hj⟩
    · exact ⟨i, hin, hi⟩
  obtain ⟨m, hmn, p, hpC, hpF⟩ := hm
  let q : C := ⟨p, hpC⟩
  have hsep : Disjoint (G n) (G m) := (hdisjoint hmn.symm).preimage Subtype.val
  obtain ⟨U, V, hU, hV, hnU, hmV, hUV⟩ :=
    normal_separation (hGclosed n) (hGclosed m) hsep
  have hclV : Disjoint (closure V) U := hUV.symm.closure_left hU
  have hproper : closure V ≠ univ := by
    intro heq
    obtain ⟨z, hzC, hzF⟩ := not_disjoint_iff_nonempty_inter.mp hmiss
    exact disjoint_left.mp hclV (heq ▸ mem_univ (⟨z, hzC⟩ : C)) (hnU hzF)
  have hqV : q ∈ V := hmV hpF
  obtain ⟨K, hKcompact, hKconnected, hqK, hKsub, y, hyK, hyfront⟩ :=
    BoundaryBumping.exists_subcontinuum_meeting_frontier isClosed_closure hproper
      (subset_closure hqV)
  have hyNotM : (y : X) ∉ F m := by
    intro hyM
    exact hyfront.2 (hV.subset_interior_closure (hmV hyM))
  have hKavoid : Disjoint (Subtype.val '' K) (F n) := by
    refine disjoint_left.mpr ?_
    rintro z ⟨w, hwK, rfl⟩ hzN
    exact disjoint_left.mp hclV (hKsub hwK) (hnU hzN)
  have hycover : (y : X) ∈ ⋃ k, F k := hcover ▸ mem_univ _
  obtain ⟨k, hyF⟩ := mem_iUnion.mp hycover
  have hmk : m ≠ k := by
    intro hmk
    exact hyNotM (hmk ▸ hyF)
  refine ⟨Subtype.val '' K, hKcompact.image continuous_subtype_val,
    hKconnected.image _ continuous_subtype_val.continuousOn, ?_, hKavoid,
    m, k, hmk, ⟨p, ⟨q, hqK, rfl⟩, hpF⟩, ⟨y, ⟨y, hyK, rfl⟩, hyF⟩⟩
  rintro z ⟨w, _, rfl⟩
  exact w.2

/-- Sierpiński's closed-partition theorem for a nonempty compact connected
Hausdorff space. Empty pieces are permitted. -/
theorem exists_eq_univ_of_nat_closed_partition
    [cX : CompactSpace X] [connX : ConnectedSpace X]
    (F : ℕ → Set X) (hclosed : ∀ n, IsClosed (F n))
    (hdisjoint : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hcover : ⋃ n, F n = univ) : ∃ n, F n = univ := by
  classical
  by_contra hwhole
  have hproper : ∀ n, F n ≠ univ := by simpa using hwhole
  obtain ⟨x⟩ := (inferInstance : Nonempty X)
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover ▸ mem_univ x)
  have hiProper : ¬ univ ⊆ F i := by
    intro hsub
    exact hproper i (Subset.antisymm (subset_univ _) hsub)
  obtain ⟨y, _, hyi⟩ := not_subset.mp hiProper
  obtain ⟨j, hyj⟩ := mem_iUnion.mp (hcover ▸ mem_univ y)
  have hij : i ≠ j := by
    intro hij
    exact hyi (hij ▸ hyj)
  let P : Set X → Prop := fun C => IsCompact C ∧ IsConnected C ∧
    ∃ a b, a ≠ b ∧ (C ∩ F a).Nonempty ∧ (C ∩ F b).Nonempty
  have hstart : P univ := ⟨isCompact_univ, isConnected_univ,
    i, j, hij, ⟨x, mem_univ x, hxi⟩, ⟨y, mem_univ y, hyj⟩⟩
  have hstep (C : {C : Set X // P C}) (n : ℕ) :
      ∃ D : {C : Set X // P C}, D.val ⊆ C.val ∧ Disjoint D.val (F n) := by
    obtain ⟨D, hDc, hDconn, hDC, hDn, hDtwo⟩ :=
      shrink_continuum F hclosed hdisjoint hcover C.2.1 C.2.2.1 C.2.2.2 n
    exact ⟨⟨D, hDc, hDconn, hDtwo⟩, hDC, hDn⟩
  choose next hnextSub hnextAvoid using hstep
  let seq : ℕ → {C : Set X // P C} := Nat.rec ⟨univ, hstart⟩ (fun n C => next C n)
  have hsub (n : ℕ) : (seq (n + 1)).val ⊆ (seq n).val := hnextSub (seq n) n
  have havoid (n : ℕ) : Disjoint (seq (n + 1)).val (F n) := hnextAvoid (seq n) n
  obtain ⟨z, hz⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n => (seq n).val) hsub (fun n => (seq n).2.2.1.nonempty)
    (seq 0).2.1 (fun n => (seq n).2.1.isClosed)
  obtain ⟨n, hzn⟩ := mem_iUnion.mp (hcover ▸ mem_univ z)
  exact disjoint_left.mp (havoid n) (mem_iInter.mp hz (n + 1)) hzn

/-- Any countable closed partition of a continuum has a piece equal to the
whole space. This includes finite index types and allows empty pieces. -/
theorem exists_eq_univ_of_countable_closed_partition
    [cX : CompactSpace X] [connX : ConnectedSpace X] {ι : Type v} [countI : Countable ι]
    (F : ι → Set X) (hclosed : ∀ i, IsClosed (F i))
    (hdisjoint : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hcover : ⋃ i, F i = univ) : ∃ i, F i = univ := by
  classical
  obtain ⟨e, he⟩ := exists_injective_nat ι
  let G : ℕ → Set X := fun n => ⋃ i, ⋃ (_ : e i = n), F i
  have hGat (i : ι) : G (e i) = F i := by
    ext x
    simp only [G, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨j, hj, hxj⟩
      exact he hj ▸ hxj
    · intro hxi
      exact ⟨i, rfl, hxi⟩
  have hGempty (n : ℕ) (hn : ¬ ∃ i, e i = n) : G n = ∅ := by
    ext x
    simp only [G, mem_iUnion, exists_prop, mem_empty_iff_false, iff_false]
    rintro ⟨i, hi, _⟩
    exact hn ⟨i, hi⟩
  have hGclosed (n : ℕ) : IsClosed (G n) := by
    by_cases hn : ∃ i, e i = n
    · obtain ⟨i, rfl⟩ := hn
      rw [hGat]
      exact hclosed i
    · rw [hGempty n hn]
      exact isClosed_empty
  have hGdisjoint : Pairwise (fun m n => Disjoint (G m) (G n)) := by
    intro m n hmn
    refine disjoint_left.mpr ?_
    intro x hxm hxn
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxm
    obtain ⟨him, hxi⟩ := mem_iUnion.mp hxi
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxn
    obtain ⟨hjn, hxj⟩ := mem_iUnion.mp hxj
    have hij : i ≠ j := by
      intro hij
      exact hmn (him.symm.trans (hij ▸ hjn))
    exact disjoint_left.mp (hdisjoint hij) hxi hxj
  have hGcover : ⋃ n, G n = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i, hxi⟩ := mem_iUnion.mp (hcover ▸ mem_univ x)
    exact mem_iUnion.mpr ⟨e i, hGat i ▸ hxi⟩
  obtain ⟨n, hn⟩ := exists_eq_univ_of_nat_closed_partition G hGclosed hGdisjoint hGcover
  have hindex : ∃ i, e i = n := by
    by_contra hnindex
    have : (univ : Set X) = ∅ := hn.symm.trans (hGempty n hnindex)
    exact univ_nonempty.ne_empty this
  obtain ⟨i, rfl⟩ := hindex
  exact ⟨i, (hGat i).symm.trans hn⟩

/-- A continuous choice among a countable family of continuous functions that
are everywhere pairwise distinct uses one fixed function on a continuum. -/
theorem continuous_choice_eq_one [cX : CompactSpace X] [connX : ConnectedSpace X]
    {Y : Type v} [tY : TopologicalSpace Y] [t2Y : T2Space Y]
    {ι : Type w} [countI : Countable ι] (f : ι → X → Y) (g : X → Y)
    (hf : ∀ i, Continuous (f i)) (hg : Continuous g)
    (hdistinct : ∀ x, Pairwise (fun i j => f i x ≠ f j x))
    (hchoice : ∀ x, ∃ i, g x = f i x) : ∃ i, g = f i := by
  let F : ι → Set X := fun i => {x | g x = f i x}
  have hclosed (i : ι) : IsClosed (F i) := isClosed_eq hg (hf i)
  have hdisjoint : Pairwise (fun i j => Disjoint (F i) (F j)) := by
    intro i j hij
    exact disjoint_left.mpr fun x hxi hxj => hdistinct x hij (hxi.symm.trans hxj)
  have hcover : ⋃ i, F i = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := hchoice x
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨i, hi⟩ := exists_eq_univ_of_countable_closed_partition F hclosed hdisjoint hcover
  refine ⟨i, funext fun x => ?_⟩
  exact (show x ∈ F i from hi ▸ mem_univ x)

end Sierpinski
