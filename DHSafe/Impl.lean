import DHSafe.Spec

namespace Impl

def powMod (g e p : Nat) : Nat := sorry
def defaultGroup : DHGroup := sorry
def mkSecret (G : DHGroup) (a : Nat) : Option (Secret G) := sorry
def publicOf (G : DHGroup) (s : Secret G) : PublicValue G := sorry
def parsePublic (G : DHGroup) (y : Nat) : Option (PublicValue G) := sorry
def shared (G : DHGroup) (s : Secret G) (P : PublicValue G) : Nat := sorry

theorem powMod_correct_impl : PowModCorrect powMod := sorry
theorem scheme_correct_impl : SchemeCorrect mkSecret publicOf parsePublic shared := sorry
theorem key_correct_impl : KeyCorrect publicOf shared := sorry

-- locked section: guards against weakening the theorems above
theorem powMod_correct : PowModCorrect powMod := powMod_correct_impl
theorem scheme_correct : SchemeCorrect mkSecret publicOf parsePublic shared := scheme_correct_impl
theorem key_correct : KeyCorrect publicOf shared := key_correct_impl

end Impl
