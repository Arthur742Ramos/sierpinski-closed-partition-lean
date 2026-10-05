/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak,
Ruy Jose Guerra Barretto de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy Jose Guerra Barretto de Queiroz
-/
module

public import Mathlib.Topology.Separation.Regular

/-! Independent statement contracts. The three theorem holes are intentional. -/

@[expose] public section

open Set

universe u v w

namespace Sierpinski

variable {X : Type u} [tX : TopologicalSpace X] [t2X : T2Space X]

theorem exists_eq_univ_of_nat_closed_partition
    [cX : CompactSpace X] [connX : ConnectedSpace X]
    (F : ℕ → Set X) (hclosed : ∀ n, IsClosed (F n))
    (hdisjoint : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hcover : ⋃ n, F n = univ) : ∃ n, F n = univ := by
  sorry

theorem exists_eq_univ_of_countable_closed_partition
    [cX : CompactSpace X] [connX : ConnectedSpace X] {ι : Type v} [countI : Countable ι]
    (F : ι → Set X) (hclosed : ∀ i, IsClosed (F i))
    (hdisjoint : Pairwise (fun i j => Disjoint (F i) (F j)))
    (hcover : ⋃ i, F i = univ) : ∃ i, F i = univ := by
  sorry

theorem continuous_choice_eq_one [cX : CompactSpace X] [connX : ConnectedSpace X]
    {Y : Type v} [tY : TopologicalSpace Y] [t2Y : T2Space Y]
    {ι : Type w} [countI : Countable ι] (f : ι → X → Y) (g : X → Y)
    (hf : ∀ i, Continuous (f i)) (hg : Continuous g)
    (hdistinct : ∀ x, Pairwise (fun i j => f i x ≠ f j x))
    (hchoice : ∀ x, ∃ i, g x = f i x) : ∃ i, g = f i := by
  sorry

end Sierpinski
