import DHSafe.Spec

namespace Impl

/-! ## Modular exponentiation -/

/-- Square-and-multiply with an explicit fuel parameter, so the definition is
    structurally recursive and the kernel can evaluate it. Invariant: the result is
    `acc * b ^ e % p`, provided `e < fuel`. -/
def powModAux : Nat → Nat → Nat → Nat → Nat → Nat
  | 0, _, _, p, acc => acc % p
  | fuel + 1, b, e, p, acc =>
    if e = 0 then acc % p
    else powModAux fuel (b * b % p) (e / 2) p (if e % 2 = 1 then acc * b % p else acc)

def powMod (g e p : Nat) : Nat := powModAux (e + 1) (g % p) e p (1 % p)

theorem powModAux_eq (p : Nat) :
    ∀ fuel b e acc, e < fuel → powModAux fuel b e p acc = acc * b ^ e % p := by
  intro fuel
  induction fuel with
  | zero => intro b e acc h; omega
  | succ fuel ih =>
    intro b e acc h
    unfold powModAux
    split_ifs with he hodd
    · subst he; simp
    · rw [ih _ _ _ (by omega)]
      have key : b ^ e = (b * b) ^ (e / 2) * b ^ (e % 2) := by
        rw [← pow_two, ← pow_mul, ← pow_add, Nat.div_add_mod]
      rw [key, hodd]
      apply (ZMod.natCast_eq_natCast_iff' _ _ p).1
      push_cast [ZMod.natCast_mod]
      ring
    · rw [ih _ _ _ (by omega)]
      have key : b ^ e = (b * b) ^ (e / 2) * b ^ (e % 2) := by
        rw [← pow_two, ← pow_mul, ← pow_add, Nat.div_add_mod]
      rw [key, show e % 2 = 0 by omega]
      apply (ZMod.natCast_eq_natCast_iff' _ _ p).1
      push_cast [ZMod.natCast_mod]
      ring

theorem powMod_correct_impl : PowModCorrect powMod := by
  intro g e p _
  unfold powMod powModRef
  rw [powModAux_eq p _ _ _ _ (Nat.lt_succ_self e)]
  apply (ZMod.natCast_eq_natCast_iff' _ _ p).1
  push_cast [ZMod.natCast_mod]
  ring

/-! ## Helpers relating `Nat` arithmetic mod `n` to `ZMod n` -/

theorem mod_eq_one_iff {x n : Nat} (hn : 1 < n) : x % n = 1 ↔ (x : ZMod n) = 1 := by
  rw [show (1 : ZMod n) = ((1 : Nat) : ZMod n) from Nat.cast_one.symm,
    ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hn]

theorem zmod_pow_eq_one_iff (a k n : Nat) (hn : 1 < n) :
    (a : ZMod n) ^ k = 1 ↔ powMod a k n = 1 := by
  rw [← Nat.cast_pow, ← mod_eq_one_iff hn, powMod_correct_impl _ _ _ (by omega)]
  rfl

theorem prime_dvd_mul_cases {r m n : Nat} (hr : r.Prime) (hm : m.Prime) (h : r ∣ m * n) :
    r = m ∨ r ∣ n := by
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr hm).1 h)
  · exact Or.inr h

/-! ## Default group parameters -/

/-- Lucas certificate for `q`, with witness 13 and
    `q - 1 = 2 * 154373 * 181277 * 203449 * 205391 * 273073 * 321577 * 504901`. -/
theorem q_prime : Nat.Prime 103693369189574614053993095518446676439 := by
  refine lucas_primality _ ((13 : Nat) : ZMod _) ?_ ?_
  · rw [zmod_pow_eq_one_iff _ _ _ (by norm_num)]
    decide +kernel
  · intro r hr hd
    have hfac : (103693369189574614053993095518446676439 - 1 : Nat) =
        2 * (154373 * (181277 * (203449 * (205391 * (273073 * (321577 * 504901)))))) := by
      norm_num
    rw [hfac] at hd
    rcases prime_dvd_mul_cases hr (by norm_num) hd with rfl | hd
    rotate_left
    rcases prime_dvd_mul_cases hr (by norm_num) hd with rfl | hd
    rotate_left
    rcases prime_dvd_mul_cases hr (by norm_num) hd with rfl | hd
    rotate_left
    rcases prime_dvd_mul_cases hr (by norm_num) hd with rfl | hd
    rotate_left
    rcases prime_dvd_mul_cases hr (by norm_num) hd with rfl | hd
    rotate_left
    rcases prime_dvd_mul_cases hr (by norm_num) hd with rfl | hd
    rotate_left
    rcases prime_dvd_mul_cases hr (by norm_num) hd with rfl | hd
    rotate_left
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 hd
    all_goals
      rw [Ne, zmod_pow_eq_one_iff _ _ _ (by norm_num)]
      decide +kernel

/-- Lucas certificate for the safe prime `p = 2q + 1`, with witness 11. -/
theorem p_prime : Nat.Prime 207386738379149228107986191036893352879 := by
  refine lucas_primality _ ((11 : Nat) : ZMod _) ?_ ?_
  · rw [zmod_pow_eq_one_iff _ _ _ (by norm_num)]
    decide +kernel
  · intro r hr hd
    have hfac : (207386738379149228107986191036893352879 - 1 : Nat) =
        2 * 103693369189574614053993095518446676439 := by
      norm_num
    rw [hfac] at hd
    rcases prime_dvd_mul_cases hr (by norm_num) hd with rfl | hd
    rotate_left
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hr q_prime).1 hd
    all_goals
      rw [Ne, zmod_pow_eq_one_iff _ _ _ (by norm_num)]
      decide +kernel

def defaultGroup : DHGroup where
  p := 207386738379149228107986191036893352879
  g := 4
  q := 103693369189574614053993095518446676439
  good := by
    refine ⟨p_prime, q_prime, by norm_num, by unfold qFloor; norm_num, by norm_num,
      by norm_num, ?_⟩
    rw [← powMod_correct_impl _ _ _ (by norm_num)]
    decide +kernel

/-! ## Scheme -/

def mkSecret (G : DHGroup) (a : Nat) : Option (Secret G) :=
  if h : 1 ≤ a ∧ a < G.q then some ⟨a, h⟩ else none

/-- For `1 ≤ a < q`, `g ^ a mod p` is a valid public value: `g` has order exactly `q`
    in `(ZMod p)ˣ`, so `g ^ a` is neither `0`, `1` nor `-1`, and lies in the
    order-`q` subgroup. -/
theorem valid_pow (G : DHGroup) (a : Nat) (ha : 1 ≤ a ∧ a < G.q) :
    ValidPublic G (powMod G.g a G.p) := by
  obtain ⟨hp, hq, hpq, hfloor, hg1, hgp, hgq⟩ := G.good
  have := Fact.mk hp
  have := Fact.mk hq
  have hq2 : 2 < G.q := by unfold qFloor at hfloor; omega
  have hp1 : 1 < G.p := hp.one_lt
  rw [powMod_correct_impl _ _ _ hp.pos]
  unfold ValidPublic powModRef at *
  set x : ZMod G.p := (G.g : ZMod G.p) with hx
  have hxq : x ^ G.q = 1 := by
    rw [mod_eq_one_iff hp1] at hgq
    push_cast at hgq
    exact hgq
  have hx1 : x ≠ 1 := by
    intro h
    rw [hx, show (1 : ZMod G.p) = ((1 : Nat) : ZMod G.p) from Nat.cast_one.symm,
      ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hgp, Nat.mod_eq_of_lt hp1] at h
    omega
  have hord : orderOf x = G.q := orderOf_eq_prime hxq hx1
  have hcast : ((G.g ^ a : Nat) : ZMod G.p) = x ^ a := by
    push_cast; rfl
  refine ⟨?_, ?_, ?_⟩
  · -- `g ^ a mod p` is neither 0 nor 1
    have hne0 : G.g ^ a % G.p ≠ 0 := by
      intro h
      have h' := congrArg (Nat.cast : Nat → ZMod G.p) h
      rw [ZMod.natCast_mod, hcast, Nat.cast_zero] at h'
      have hx0 : x = 0 := pow_eq_zero_iff (by omega) |>.1 h'
      rw [hx, ZMod.natCast_eq_zero_iff] at hx0
      exact absurd (Nat.le_of_dvd (by omega) hx0) (by omega)
    have hne1 : G.g ^ a % G.p ≠ 1 := by
      intro h
      rw [mod_eq_one_iff hp1, hcast, ← orderOf_dvd_iff_pow_eq_one, hord] at h
      exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
    omega
  · -- `g ^ a mod p ≠ p - 1`, else `g ^ (2a) = 1` and `q ∣ 2a`
    have hlt : G.g ^ a % G.p < G.p := Nat.mod_lt _ hp.pos
    have hne : G.g ^ a % G.p ≠ G.p - 1 := by
      intro h
      have h' := congrArg (Nat.cast : Nat → ZMod G.p) h
      rw [ZMod.natCast_mod, hcast, Nat.cast_sub hp1.le, ZMod.natCast_self, Nat.cast_one, zero_sub] at h'
      have h2 : x ^ (2 * a) = 1 := by rw [mul_comm, pow_mul, h']; simp
      rw [← orderOf_dvd_iff_pow_eq_one, hord] at h2
      rcases (Nat.Prime.dvd_mul hq).1 h2 with h2 | h2
      · exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)
      · exact absurd (Nat.le_of_dvd (by omega) h2) (by omega)
    omega
  · -- `(g ^ a) ^ q = (g ^ q) ^ a = 1`
    rw [mod_eq_one_iff hp1]
    push_cast [ZMod.natCast_mod]
    rw [← hx, ← pow_mul, mul_comm, pow_mul, hxq, one_pow]

def publicOf (G : DHGroup) (s : Secret G) : PublicValue G :=
  ⟨powMod G.g s.a G.p, valid_pow G s.a s.inRange⟩

def parsePublic (G : DHGroup) (y : Nat) : Option (PublicValue G) :=
  if h : 1 < y ∧ y + 1 < G.p ∧ powMod y G.q G.p = 1 then
    some ⟨y, by
      unfold ValidPublic
      rw [← powMod_correct_impl _ _ _ G.good.1.pos]
      exact h⟩
  else none

def shared (G : DHGroup) (s : Secret G) (P : PublicValue G) : Nat :=
  powMod P.y s.a G.p

theorem scheme_correct_impl : SchemeCorrect mkSecret publicOf parsePublic shared := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro G a s h
    unfold mkSecret at h
    split_ifs at h
    cases h
    rfl
  · intro G a
    unfold mkSecret
    split_ifs with h <;> simp [h]
  · intro G s
    exact powMod_correct_impl _ _ _ G.good.1.pos
  · intro G y P h
    unfold parsePublic at h
    split_ifs at h
    cases h
    rfl
  · intro G y
    unfold parsePublic ValidPublic
    rw [← powMod_correct_impl _ _ _ G.good.1.pos]
    split_ifs with h <;> simp [h]
  · intro G s P
    exact powMod_correct_impl _ _ _ G.good.1.pos

theorem key_correct_impl : KeyCorrect publicOf shared := by
  intro G sA sB
  unfold shared publicOf
  simp only
  rw [powMod_correct_impl _ _ _ G.good.1.pos, powMod_correct_impl _ _ _ G.good.1.pos]
  unfold powModRef
  rw [← Nat.pow_mod, ← pow_mul, mul_comm sB.a sA.a]

-- locked section: guards against weakening the theorems above
theorem powMod_correct : PowModCorrect powMod := powMod_correct_impl
theorem scheme_correct : SchemeCorrect mkSecret publicOf parsePublic shared := scheme_correct_impl
theorem key_correct : KeyCorrect publicOf shared := key_correct_impl

end Impl
