import RequestProject.Disjoint

/-!
# The exact zero count on a finite union of model disks (`p = 3/2`)

Section 8 of the round's specification.  Combining

* `model_disk_zero_count_one_p32` — exactly one zero, and it is simple, in each model
  disk attached to an admissible crossing index, and
* `model_disks_pairwise_disjoint_p32` — those disks are pairwise disjoint,

the number of zeros of `F_{3/2}^{(n)}` in the union of a finite family of admissible
model disks equals the number of disks.  Since every one of these zeros is simple, this
is also the total multiplicity.
-/

namespace SparseFock

open scoped BigOperators Nat
open Classical

set_option maxHeartbeats 1000000 in
/-- **Exact zero count on a finite union of model disks** (`p = 3/2`).

For every fixed annulus there are `c` and `N` such that for `n ≥ N` and every finite
family `I` of admissible index pairs `(j, ℓ)` (`a ≤ ρ_j ≤ b`, `ℓ < q_j`), the set of
zeros of `F_{3/2}^{(n)}` inside `⋃_{i ∈ I} D_i` has exactly `#I` elements; moreover each
of them is a simple zero, so the total multiplicity is also `#I`. -/
theorem zero_count_model_disk_union_p32 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ I : Finset (ℕ × ℕ),
      (∀ i ∈ I, 1 ≤ i.1 ∧ n ≤ nu (3/2) i.1 ∧ a ≤ rho (3/2) n i.1 ∧
          rho (3/2) n i.1 ≤ b ∧ i.2 < qgap (3/2) i.1) →
      ({z : ℂ | (∃ i ∈ I, z ∈ modelDisk c n i.1 i.2) ∧
          iteratedDeriv n (F (3/2)) z = 0}).ncard = I.card ∧
      (∀ z : ℂ, (∃ i ∈ I, z ∈ modelDisk c n i.1 i.2) →
          iteratedDeriv n (F (3/2)) z = 0 →
          deriv (iteratedDeriv n (F (3/2))) z ≠ 0) := by
  classical
  obtain ⟨c, hc, hc1, N₁, hN₁⟩ := model_disk_zero_count_one_p32 ha hab
  obtain ⟨N₂, hN₂⟩ := model_disks_pairwise_disjoint_p32 ha hab hc hc1
  refine ⟨c, hc, hc1, max N₁ N₂, fun n hn I hI => ?_⟩
  have hn1 : N₁ ≤ n := le_trans (le_max_left _ _) hn
  have hn2 : N₂ ≤ n := le_trans (le_max_right _ _) hn
  have huniq : ∀ i ∈ I, ∃! z : ℂ,
      z ∈ modelDisk c n i.1 i.2 ∧ iteratedDeriv n (F (3/2)) z = 0 := by
    intro i hi
    obtain ⟨h1, h2, h3, h4, -⟩ := hI i hi
    exact (hN₁ n hn1 i.1 h1 h2 h3 h4 i.2).1
  refine ⟨?_, ?_⟩
  · -- the counting statement
    set g : ℕ × ℕ → ℂ := fun i =>
      if h : ∃ z : ℂ, z ∈ modelDisk c n i.1 i.2 ∧ iteratedDeriv n (F (3/2)) z = 0
        then h.choose else 0 with hg
    have hgspec : ∀ i ∈ I,
        g i ∈ modelDisk c n i.1 i.2 ∧ iteratedDeriv n (F (3/2)) (g i) = 0 := by
      intro i hi
      have hex : ∃ z : ℂ, z ∈ modelDisk c n i.1 i.2 ∧ iteratedDeriv n (F (3/2)) z = 0 :=
        (huniq i hi).exists
      rw [hg]
      simp only [dif_pos hex]
      exact hex.choose_spec
    have hgeq : ∀ i ∈ I, ∀ z : ℂ,
        z ∈ modelDisk c n i.1 i.2 → iteratedDeriv n (F (3/2)) z = 0 → z = g i := by
      intro i hi z hz1 hz2
      obtain ⟨w, -, hwu⟩ := huniq i hi
      rw [hwu z ⟨hz1, hz2⟩, hwu (g i) (hgspec i hi)]
    have hset : {z : ℂ | (∃ i ∈ I, z ∈ modelDisk c n i.1 i.2) ∧
        iteratedDeriv n (F (3/2)) z = 0} = ↑(I.image g) := by
      ext z
      simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe]
      constructor
      · rintro ⟨⟨i, hi, hzi⟩, hz0⟩
        exact ⟨i, hi, (hgeq i hi z hzi hz0).symm⟩
      · rintro ⟨i, hi, rfl⟩
        obtain ⟨hd, h0⟩ := hgspec i hi
        exact ⟨⟨i, hi, hd⟩, h0⟩
    rw [hset, Set.ncard_coe_finset]
    refine Finset.card_image_of_injOn ?_
    intro i hi i' hi' heq
    by_contra hne
    have hiI : i ∈ I := by simpa using hi
    have hi'I : i' ∈ I := by simpa using hi'
    obtain ⟨h1, h2, h3, h4, h5⟩ := hI i hiI
    obtain ⟨h1', h2', h3', h4', h5'⟩ := hI i' hi'I
    have hor : i.1 ≠ i'.1 ∨ i.2 ≠ i'.2 := by
      by_contra hcon
      push_neg at hcon
      exact hne (Prod.ext_iff.2 ⟨hcon.1, hcon.2⟩)
    have hdisj := hN₂ n hn2 i.1 i'.1 i.2 i'.2 h1 h2 h3 h4 h1' h2' h3' h4' h5 h5' hor
    have hmem := (hgspec i hiI).1
    have hmem' := (hgspec i' hi'I).1
    rw [heq] at hmem
    exact (Set.disjoint_left.1 hdisj hmem) hmem'
  · -- simplicity of each of them
    rintro z ⟨i, hi, hzi⟩ hz0
    obtain ⟨h1, h2, h3, h4, -⟩ := hI i hi
    exact (hN₁ n hn1 i.1 h1 h2 h3 h4 i.2).2 z hzi hz0

end SparseFock
