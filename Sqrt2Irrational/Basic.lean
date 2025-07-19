import Mathlib
import Sqrt2Irrational.Helpers

open Real
open Int

open Classical in
theorem sqrt_2_is_irrational : Irrational √2 := by
  apply (irrational_iff_ne_rational √2).mpr
  apply byContradiction
  intro h
  push_neg at h
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, √2 = a / b := h
  obtain ⟨a'', ha''_eq⟩ : ∃a'' : ℚ, a'' = a := by norm_num
  obtain ⟨b'', hb''_eq⟩ : ∃b'' : ℚ, b'' = b := by norm_num
  have hrational_equiv: a'' / b'' = a / b := by simp [ha''_eq, hb''_eq]
  by_cases hb_zero : (b : ℝ) = 0
  · rw [hb_zero] at hab
    have h₄ : a / 0 = 0 := by simp
    have h₅ : √2 = 0 := by
      calc
        √2 = a / 0 := by simp [hab]
         _ = 0 := by simp
    norm_num at h₅
  · push_neg at hb_zero
    have hb_zero : b ≠ 0 := by
      intro h_b_eq_zero
      refine hb_zero ?_
      simp [h_b_eq_zero]
    obtain ⟨a', b', h_coprime, h_eq, hb'_non_zero⟩ := by
      apply exists_reduced_rational_for_rational a b hb_zero
    have h_eq_ℝ : (a : ℝ) / b = a' / b' := by
      norm_cast
      rify [h_eq]
      calc
        (a : ℝ) / b = Rat.cast ((a : ℚ) / b) := by norm_cast
                  _ = Rat.cast ((a' : ℚ) / b') := by simp [h_eq]
                  _ = a' / b' := by norm_num
    have : √2 = (a' : ℝ) / b' := by
      calc
        √2 = a / b := by apply hab
         _ = a' / b' := by simp [h_eq_ℝ]
    have hab : 2 * b'^2 = a'^2 :=
        by apply transform_sq_eq_rational a' b' hb'_non_zero this
    rcases Int.even_or_odd a' with h_even | h_odd
    · let ⟨kₐ, hkₐ⟩ := h_even
      have hkₐ : a' = 2 * kₐ := by calc
        a' = kₐ + kₐ := hkₐ
        _ = 2 * kₐ := by ring
      have : 2 * b'^2 = 4 * kₐ^2 := by
        calc
          2 * b'^2 = a'^2 := by exact hab
                _ = (2 * kₐ)^2 := by congr 1
                _ = 4 * kₐ^2 := by ring
      have hkb : 2 * b'^2 = 2 * (2 * kₐ^2) := by
        calc
          2 * b'^2 = 4 * kₐ^2 := by exact this
                _ = 2 * (2 * kₐ^2) := by ring
      have hkb : b'^2 = 2 * kₐ^2 := by exact mul_left_cancel₀ (by norm_num) hkb
      have hkb : 2 ∣ b'^2 := by simp [hkb]
      have hkb : 2 ∣ b' := by apply Prime.dvd_of_dvd_pow prime_two hkb
      have hb_even : Even b' := by apply even_iff_two_dvd.mpr hkb
      have : ¬IsCoprime a' b' := not_coprime_if_both_even a' b' h_even hb_even
      absurd this
      exact h_coprime
    · have ⟨kₐ, h_kₐ⟩ : ∃kₐ, a' = 2 * kₐ + 1  := by apply h_odd
      have h_eq' : 2 * b' ^ 2 = 2 * (2 * kₐ ^ 2 + 2 * kₐ) + 1 := by calc
        2 * b'^2 = a'^2 := by apply hab
              _ = (2 * kₐ + 1)^2 := by rw [h_kₐ]
              _ = 4 * kₐ ^ 2 + 4 * kₐ + 1 := by ring
              _ = 2 * (2 * kₐ ^ 2 + 2 * kₐ) + 1 := by ring
      have h1 : Even (2 * b'^2) := ⟨b'^2, by ring⟩
      have h2 : Odd (2 * (2 * kₐ^2 + 2 * kₐ) + 1) := ⟨2 * kₐ^2 + 2 * kₐ, by ring⟩
      rw [←h_eq'] at h2
      have h2 : ¬Even (2 * b'^2) := by
        apply Int.not_even_iff_odd.mpr h2
      absurd h2
      exact h1
