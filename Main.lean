import DH.Impl

def p : Nat := 2 ^ 127 - 1
def g : Nat := 3

-- fixed ~120-bit secrets
def a : Nat := 0xB7E151628AED2A6ABF7158809CF4F3
def b : Nat := 0x9E3779B97F4A7C15F39CC0605CEDC8

def main : IO Unit := do
  let A := Impl.publicKey p g a
  let B := Impl.publicKey p g b
  IO.println s!"A = g^a mod p = {A}"
  IO.println s!"B = g^b mod p = {B}"
  IO.println s!"validate A: {Impl.validate p A}"
  IO.println s!"validate B: {Impl.validate p B}"
  let sA := Impl.sharedSecret p B a
  let sB := Impl.sharedSecret p A b
  IO.println s!"Alice's shared secret (B^a mod p) = {sA}"
  IO.println s!"Bob's shared secret   (A^b mod p) = {sB}"
  IO.println s!"shared secrets equal: {sA == sB}"
