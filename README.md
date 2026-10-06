# Lean for Software Engineering

Lean 4 projects applying formal verification to software engineering.

- [`dh`](dh/): verified Diffie-Hellman key exchange (square-and-multiply `powMod` with correctness proofs).
- [`dhsafe`](dhsafe/): Diffie-Hellman over a 128-bit safe-prime group, with primality of the parameters proved via Lucas certificates and full public-value validation (toy parameter size).
