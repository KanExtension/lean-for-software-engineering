import DHSafe.Impl

/-- Big-endian conversion of a byte array to a natural number. -/
def bytesToNat (b : ByteArray) : Nat :=
  b.foldl (fun acc x => acc * 256 + x.toNat) 0

/-- Draw a fresh secret from 32 bytes of OS randomness, mapped into `[1, q - 1]`. -/
def freshSecret (G : DHGroup) : IO (Option (Secret G)) := do
  let bytes ← IO.getRandomBytes 32
  let a := bytesToNat bytes % (G.q - 1) + 1
  return Impl.mkSecret G a

def main : IO UInt32 := do
  let G := Impl.defaultGroup
  IO.println s!"p = {G.p}"
  IO.println s!"q = {G.q}"
  IO.println s!"g = {G.g}"

  let some sA ← freshSecret G
    | IO.eprintln "error: failed to create Alice's secret"; return 1
  let some sB ← freshSecret G
    | IO.eprintln "error: failed to create Bob's secret"; return 1
  IO.println s!"Alice secret (demo only) = {sA.a}"
  IO.println s!"Bob secret   (demo only) = {sB.a}"

  let pubA := Impl.publicOf G sA
  let pubB := Impl.publicOf G sB
  IO.println s!"Alice public = {pubA.y}"
  IO.println s!"Bob public   = {pubB.y}"

  -- Transmission: only the plain numbers cross the wire; each receiver re-validates.
  let wireA : Nat := pubA.y
  let wireB : Nat := pubB.y
  let some bobFromAlice := Impl.parsePublic G wireA
    | IO.eprintln "error: Bob rejected Alice's public value"; return 1
  let some aliceFromBob := Impl.parsePublic G wireB
    | IO.eprintln "error: Alice rejected Bob's public value"; return 1

  let keyA := Impl.shared G sA aliceFromBob
  let keyB := Impl.shared G sB bobFromAlice
  IO.println s!"Alice key = {keyA}"
  IO.println s!"Bob key   = {keyB}"
  IO.println s!"keys equal: {keyA == keyB}"

  IO.println "parsePublic rejection table:"
  for y in [0, 1, G.p - 1, G.p, G.p + 1, 2, 3, G.g] do
    let verdict := if (Impl.parsePublic G y).isSome then "accepted" else "rejected"
    IO.println s!"  y = {y}: {verdict}"
  return 0
