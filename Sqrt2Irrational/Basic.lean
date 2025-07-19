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

  have hb_zero : b ≠ 0 := by
    apply byContradiction
    intro hb_non_zero
    push_neg at hb_non_zero
    rw [hb_non_zero] at hab
    have h₄ : a / 0 = 0 := by simp
    have h₅ : √2 = 0 := by
      calc
        √2 = a / 0 := by simp [hab]
        _ = 0 := by simp
    norm_num at h₅

  obtain ⟨a', b', h_coprime, h_eq, hb'_non_zero⟩ := by
    apply exists_reduced_rational_for_rational a b hb_zero

  -- #check (h_coprime : IsCoprime a' b')
  -- #check (h_eq : (a : ℚ) / b = a' / b')
  -- #check (hb'_non_zero : b' ≠ 0)

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

  -- transform our goal to proving absurdity of a claim on a reduced rational
  -- and it's numerator a' and denominator b'
  have hab : 2 * b'^2 = a'^2 := by
    apply transform_sq_eq_rational a' b' hb'_non_zero this


  rcases Int.even_or_odd a' with h_even | h_odd
  · -- a' is even
    let ⟨kₐ, hkₐ⟩ := h_even
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
    -- extract that a' and b' are not coprime since both a' and b' are even
    have hkb : b'^2 = 2 * kₐ^2 := by exact mul_left_cancel₀ (by norm_num) hkb
    have hkb : 2 ∣ b'^2 := by simp [hkb]
    have hkb : 2 ∣ b' := by apply Prime.dvd_of_dvd_pow prime_two hkb
    have hb_even : Even b' := by apply even_iff_two_dvd.mpr hkb
    have : ¬IsCoprime a' b' := not_coprime_if_both_even a' b' h_even hb_even
    contradiction
  · -- a' is odd
    have ⟨kₐ, h_kₐ⟩ : ∃kₐ, a' = 2 * kₐ + 1  := by apply h_odd
    -- extract contradiction since 2 * b'^2 is even but 2 * a'^2 + 1 is odd
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
    contradiction
