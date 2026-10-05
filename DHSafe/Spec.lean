import Mathlib

/-- Reference modular exponentiation: mathematically transparent,
    computationally infeasible for large exponents. Specification only: never evaluate. -/
def powModRef (g e p : Nat) : Nat := g ^ e % p

def PowModCorrect (powMod : Nat → Nat → Nat → Nat) : Prop :=
  ∀ (g e p : Nat), 0 < p → powMod g e p = powModRef g e p

/-- Size floor on the subgroup order. TOY VALUE: with p = 2q + 1 it forces p > 2^127,
    far below the 2048-bit / 224-bit minimum for real use. -/
def qFloor : Nat := 2 ^ 126

/-- Acceptable domain parameters: a safe prime p = 2q + 1, and a generator g of the
    order-q subgroup (g ≠ 1 and g^q ≡ 1 with q prime force order exactly q). -/
def GoodGroup (p g q : Nat) : Prop :=
  Nat.Prime p ∧ Nat.Prime q ∧ p = 2 * q + 1 ∧ qFloor < q ∧
  1 < g ∧ g < p ∧ powModRef g q p = 1

structure DHGroup where
  p : Nat
  g : Nat
  q : Nat
  good : GoodGroup p g q

structure Secret (G : DHGroup) where
  a : Nat
  inRange : 1 ≤ a ∧ a < G.q

/-- Full public-value validation (NIST SP 800-56A): in range and in the order-q subgroup. -/
def ValidPublic (G : DHGroup) (y : Nat) : Prop :=
  1 < y ∧ y + 1 < G.p ∧ powModRef y G.q G.p = 1

structure PublicValue (G : DHGroup) where
  y : Nat
  valid : ValidPublic G y

def SchemeCorrect
    (mkSecret    : (G : DHGroup) → Nat → Option (Secret G))
    (publicOf    : (G : DHGroup) → Secret G → PublicValue G)
    (parsePublic : (G : DHGroup) → Nat → Option (PublicValue G))
    (shared      : (G : DHGroup) → Secret G → PublicValue G → Nat) : Prop :=
  (∀ (G : DHGroup) (a : Nat) (s : Secret G), mkSecret G a = some s → s.a = a) ∧
  (∀ (G : DHGroup) (a : Nat), (mkSecret G a).isSome = true ↔ (1 ≤ a ∧ a < G.q)) ∧
  (∀ (G : DHGroup) (s : Secret G), (publicOf G s).y = powModRef G.g s.a G.p) ∧
  (∀ (G : DHGroup) (y : Nat) (P : PublicValue G), parsePublic G y = some P → P.y = y) ∧
  (∀ (G : DHGroup) (y : Nat), (parsePublic G y).isSome = true ↔ ValidPublic G y) ∧
  (∀ (G : DHGroup) (s : Secret G) (P : PublicValue G), shared G s P = powModRef P.y s.a G.p)

/-- The headline guarantee: both parties derive g^(ab) mod p. -/
def KeyCorrect
    (publicOf : (G : DHGroup) → Secret G → PublicValue G)
    (shared   : (G : DHGroup) → Secret G → PublicValue G → Nat) : Prop :=
  ∀ (G : DHGroup) (sA sB : Secret G),
    shared G sA (publicOf G sB) = powModRef G.g (sA.a * sB.a) G.p
