/-- Reference modular exponentiation: mathematically transparent,
    computationally infeasible for large exponents. Never evaluate this. -/
def powModRef (g e p : Nat) : Nat := g ^ e % p

def PowModCorrect (powMod : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (g e p : Nat), 0 < p → powMod g e p = powModRef g e p

/-- Partial public-value validation (NIST SP 800-56A style): 2 ≤ y ≤ p - 2. -/
def ValidPublic (p y : Nat) : Prop := 1 < y ∧ y + 1 < p

def ValidateCorrect (validate : Nat → Nat → Bool) : Prop :=
  ∀ (p y : Nat), validate p y = true ↔ ValidPublic p y

def DHCorrect
    (publicKey : Nat → Nat → Nat → Nat)     -- p, g, own secret ↦ public value
    (sharedSecret : Nat → Nat → Nat → Nat)  -- p, peer's public value, own secret ↦ key
    : Prop :=
  ∀ (p g a b : Nat), 0 < p →
    sharedSecret p (publicKey p g b) a = sharedSecret p (publicKey p g a) b ∧
    sharedSecret p (publicKey p g b) a = powModRef g (a * b) p
