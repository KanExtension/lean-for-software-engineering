import DH.Spec

namespace Impl

/-- Modular exponentiation by square-and-multiply, halving the exponent each step.
    Every intermediate value is reduced mod `p`. -/
def powMod (g e p : Nat) : Nat :=
  if h : e = 0 then 1 % p
  else
    let r := powMod (g % p * (g % p) % p) (e / 2) p
    if e % 2 = 1 then r * (g % p) % p else r
termination_by e
decreasing_by exact Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide)

def validate (p y : Nat) : Bool := 1 < y && y + 1 < p
def publicKey (p g a : Nat) : Nat := powMod g a p
def sharedSecret (p y a : Nat) : Nat := powMod y a p

theorem powMod_eq (g e p : Nat) : powMod g e p = g ^ e % p := by
  induction e using Nat.strongRecOn generalizing g with
  | _ e ih =>
    rw [powMod]
    by_cases h : e = 0
    · subst h; simp
    · simp only [h, dite_false]
      rw [ih (e / 2) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide))]
      have hsq : (g % p * (g % p) % p) ^ (e / 2) % p = g ^ (2 * (e / 2)) % p := by
        rw [Nat.pow_mul, Nat.pow_two, Nat.pow_mod (g * g), Nat.mul_mod g g p]
      rw [hsq]
      have he := Nat.div_add_mod e 2
      split
      · next h1 =>
        rw [h1] at he
        rw [← Nat.mul_mod, ← Nat.pow_succ, Nat.succ_eq_add_one, he]
      · next h1 =>
        have h0 : e % 2 = 0 := by omega
        rw [h0, Nat.add_zero] at he
        rw [he]

theorem powMod_correct_impl : PowModCorrect powMod := by
  intro g e p _
  rw [powMod_eq]; rfl

theorem validate_correct_impl : ValidateCorrect validate := by
  intro p y
  simp [validate, ValidPublic]

theorem dh_correct_impl : DHCorrect publicKey sharedSecret := by
  intro p g a b _
  simp only [publicKey, sharedSecret, powMod_eq, powModRef]
  rw [← Nat.pow_mod, ← Nat.pow_mod, ← Nat.pow_mul, ← Nat.pow_mul, Nat.mul_comm b a]
  exact ⟨rfl, rfl⟩

-- locked section: guards against weakening the theorems above
theorem powMod_correct : PowModCorrect powMod := powMod_correct_impl
theorem validate_correct : ValidateCorrect validate := validate_correct_impl
theorem dh_correct : DHCorrect publicKey sharedSecret := dh_correct_impl

end Impl
