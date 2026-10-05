import DH.Spec

namespace Impl

def powMod (g e p : Nat) : Nat := sorry
def validate (p y : Nat) : Bool := sorry
def publicKey (p g a : Nat) : Nat := sorry
def sharedSecret (p y a : Nat) : Nat := sorry

theorem powMod_correct_impl : PowModCorrect powMod := sorry
theorem validate_correct_impl : ValidateCorrect validate := sorry
theorem dh_correct_impl : DHCorrect publicKey sharedSecret := sorry

-- locked section: guards against weakening the theorems above
theorem powMod_correct : PowModCorrect powMod := powMod_correct_impl
theorem validate_correct : ValidateCorrect validate := validate_correct_impl
theorem dh_correct : DHCorrect publicKey sharedSecret := dh_correct_impl

end Impl
