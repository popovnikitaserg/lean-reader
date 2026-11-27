import Lean

theorem have_exact (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  have hpq : p ∧ q := ⟨hp, hq⟩
  exact hpq

theorem calc_example (a b c : Nat) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  calc
    a ≤ b := hab
    _ ≤ c := hbc

theorem simp_example (p : Prop) (h : p) : p ∧ p := by
  simp [h]

theorem omega_example (a b : Nat) (hab : a < b) : a + 1 ≤ b := by
  omega

theorem alternative_example (p : Prop) (hp : p) : p := by
  first
  | exact hp
  | exact hp

theorem nested_have_example (p : Prop) (hp : p) : p := by
  have hp1 : p := by
    have hp2 : p := hp
    exact hp2
  exact hp1

theorem rw_chain_example (n : Nat) (h : n = 0) : n + 0 = 0 := by
  rw [h, Nat.zero_add]

theorem rwa_example (n : Nat) (h : n = 0) : n = 0 := by
  rwa [h]

theorem calc_mixed_example (a b c d : Nat) (hab : a = b) (hbc : b ≤ c)
    (hcd : c < d) : a < d := by
  calc
    a = b := hab
    _ ≤ c := hbc
    _ < d := hcd

theorem cases_example (p q : Prop) (h : p ∨ q) : p ∨ q := by
  cases h with
  | inl hp => exact Or.inl hp
  | inr hq => exact Or.inr hq

theorem anonymous_intro_example : ∀ n : Nat, n = n := by
  intro _
  rfl

theorem comment_example (p : Prop) (hp : p) : p := by
  -- The local assumption closes the goal.
  /- Keep block comments available to inspect as well. -/
  exact hp

def recursiveCount : Nat → Nat
  | 0 => 0
  | n + 1 => recursiveCount n + 1

def shifted (n : Nat) : Nat := n + 0

theorem shifted_type_uses_example (n : Nat) : shifted n = n := by
  simp [shifted]

theorem omega_aux_example (n : Nat) (h : n = 0) : n ≤ 0 := by
  omega
