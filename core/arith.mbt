///|
/// arith.mbt — 基礎算術：有理數、質數、因式分解、組合工具
/// Foundation arithmetic: rationals, primes, factorization, helpers.

///|
/// Greatest common divisor of two non-negative Int64 (returns 0 only for 0,0).
pub fn gcd64(a : Int64, b : Int64) -> Int64 {
  let mut x = if a < 0L { -a } else { a }
  let mut y = if b < 0L { -b } else { b }
  while y != 0L {
    let t = x % y
    x = y
    y = t
  }
  x
}

///|
/// Integer power base^exp for Int64 (exp >= 0).
pub fn pow64(base : Int64, exp : Int32) -> Int64 {
  let mut r = 1L
  let mut i = 0
  while i < exp {
    r = r * base
    i = i + 1
  }
  r
}

///|
/// Integer power base^exp for Int.
pub fn pow_int(base : Int32, exp : Int32) -> Int32 {
  let mut r = 1
  let mut i = 0
  while i < exp {
    r = r * base
    i = i + 1
  }
  r
}

///|
/// Floor of integer square root (for Int64 >= 0).
pub fn isqrt64(n : Int64) -> Int64 {
  if n <= 0L {
    return 0L
  }
  let mut x = n
  let mut y = (x + 1L) / 2L
  while y < x {
    x = y
    y = (x + n / x) / 2L
  }
  x
}

///|
/// Whether n is a perfect square.
pub fn is_square64(n : Int64) -> Bool {
  if n < 0L {
    return false
  }
  let r = isqrt64(n)
  r * r == n
}

///|
/// Sieve of Eratosthenes: all primes <= n.
pub fn primes_upto(n : Int32) -> Array[Int32] {
  let sieve : Array[Bool] = []
  let mut i = 0
  while i <= n {
    sieve.push(true)
    i = i + 1
  }
  let res : Array[Int32] = []
  let mut p = 2
  while p <= n {
    if sieve[p] {
      res.push(p)
      let mut q = p * p
      while q <= n {
        sieve[q] = false
        q = q + p
      }
    }
    p = p + 1
  }
  res
}

///|
/// Prime factorization of n > 0 as sorted (p, e) pairs.
pub fn factorize(n : Int64) -> Array[(Int64, Int32)] {
  let res : Array[(Int64, Int32)] = []
  let mut m = n
  let mut p = 2L
  while p * p <= m {
    if m % p == 0L {
      let mut e = 0
      while m % p == 0L {
        m = m / p
        e = e + 1
      }
      res.push((p, e))
    }
    p = p + 1L
  }
  if m > 1L {
    res.push((m, 1))
  }
  res
}

///|
/// Divisor sum sigma_k(n) = sum_{d|n} d^k.
pub fn sigma(n : Int32, k : Int32) -> Int64 {
  let mut s = 0L
  let mut d = 1
  while d <= n {
    if n % d == 0 {
      s = s + pow64(d.to_int64(), k)
    }
    d = d + 1
  }
  s
}

///|
/// Greatest common divisor for Int.
pub fn gcd_int(a : Int32, b : Int32) -> Int32 {
  let mut x = if a < 0 { -a } else { a }
  let mut y = if b < 0 { -b } else { b }
  while y != 0 {
    let t = x % y
    x = y
    y = t
  }
  x
}

///|
/// Extended gcd: returns (g, s, t) with s*a + t*b = g = gcd(a,b).
pub fn egcd(a : Int64, b : Int64) -> (Int64, Int64, Int64) {
  let mut old_r = a
  let mut r = b
  let mut old_s = 1L
  let mut s = 0L
  let mut old_t = 0L
  let mut t = 1L
  while r != 0L {
    let q = old_r / r
    let tmp_r = r
    r = old_r - q * r
    old_r = tmp_r
    let tmp_s = s
    s = old_s - q * s
    old_s = tmp_s
    let tmp_t = t
    t = old_t - q * t
    old_t = tmp_t
  }
  (old_r, old_s, old_t)
}

///|
/// Modular inverse of a mod m (m > 0, gcd(a, m) = 1). Returns 0 if not invertible.
pub fn mod_inverse(a : Int64, m : Int64) -> Int64 {
  let mut aa = a % m
  if aa < 0L {
    aa = aa + m
  }
  let (g, s, _) = egcd(aa, m)
  if g != 1L {
    return 0L
  }
  let mut r = s % m
  if r < 0L {
    r = r + m
  }
  r
}

///|
/// Legendre symbol (a/p) for odd prime p: 1 square, -1 non-square, 0 if p | a.
pub fn legendre(a : Int64, p : Int64) -> Int32 {
  let mut aa = a % p
  if aa < 0L {
    aa = aa + p
  }
  if aa == 0L {
    return 0
  }
  // Euler's criterion
  let mut result = 1L
  let mut base = aa
  let mut e = (p - 1L) / 2L
  while e > 0L {
    if e % 2L == 1L {
      result = result * base % p
    }
    base = base * base % p
    e = e / 2L
  }
  if result == p - 1L {
    -1
  } else {
    1
  }
}

///|
/// Rational number: normalized num/den with den > 0.
pub(all) struct Rat(Int64, Int64)

///|
/// Make a normalized rational.
pub fn Rat::make(num : Int64, den : Int64) -> Rat {
  if den == 0L {
    abort("Rat: zero denominator")
  }
  let mut n = num
  let mut d = den
  if d < 0L {
    n = -n
    d = -d
  }
  let g = gcd64(n, d)
  if g == 0L {
    Rat(0L, 1L)
  } else {
    Rat(n / g, d / g)
  }
}

///|
pub fn Rat::zero() -> Rat {
  Rat(0L, 1L)
}

///|
pub fn Rat::one() -> Rat {
  Rat(1L, 1L)
}

///|
pub fn Rat::add(self : Rat, other : Rat) -> Rat {
  Rat::make(self.0 * other.1 + other.0 * self.1, self.1 * other.1)
}

///|
pub fn Rat::sub(self : Rat, other : Rat) -> Rat {
  Rat::make(self.0 * other.1 - other.0 * self.1, self.1 * other.1)
}

///|
pub fn Rat::mul(self : Rat, other : Rat) -> Rat {
  Rat::make(self.0 * other.0, self.1 * other.1)
}

///|
pub fn Rat::div(self : Rat, other : Rat) -> Rat {
  Rat::make(self.0 * other.1, self.1 * other.0)
}

///|
pub fn Rat::neg(self : Rat) -> Rat {
  Rat(-self.0, self.1)
}

///|
pub fn Rat::abs(self : Rat) -> Rat {
  if self.0 < 0L {
    Rat(-self.0, self.1)
  } else {
    self
  }
}

///|
pub fn Rat::is_zero(self : Rat) -> Bool {
  self.0 == 0L
}

///|
pub fn Rat::to_double(self : Rat) -> Double {
  self.0.to_double() / self.1.to_double()
}

///|
pub fn Rat::to_string(self : Rat) -> String {
  if self.1 == 1L {
    "\{self.0}"
  } else {
    "\{self.0}/\{self.1}"
  }
}

///|
/// Overflow-safe modular addition: (a + b) mod m for 0 ≤ a, b < 2^62.
pub fn add_mod64(a : Int64, b : Int64, m : Int64) -> Int64 {
  let mut x = a % m
  let mut y = b % m
  if x < 0L {
    x = x + m
  }
  if y < 0L {
    y = y + m
  }
  let s = x + y
  if s >= m {
    s - m
  } else {
    s
  }
}

///|
/// Overflow-safe modular multiplication (Russian peasant), m < 2^62.
pub fn mul_mod64(a : Int64, b : Int64, m : Int64) -> Int64 {
  let mut x = a % m
  if x < 0L {
    x = x + m
  }
  let mut y = b % m
  if y < 0L {
    y = y + m
  }
  let mut acc = 0L
  while y > 0L {
    if y % 2L == 1L {
      acc = add_mod64(acc, x, m)
    }
    x = add_mod64(x, x, m)
    y = y / 2L
  }
  acc
}

///|
/// Deterministic linear congruential generator (for reproducible "randomness").
/// State stored in a 1-element array to allow mutation.
pub(all) struct LCG(Array[Int64])

///|
pub fn LCG::make(seed : Int64) -> LCG {
  let mut s = seed % 2147483647L
  if s <= 0L {
    s = s + 2147483646L
  }
  LCG([s])
}

///|
/// Next pseudo-random Int64 in [0, bound).
pub fn LCG::next(self : LCG, bound : Int64) -> Int64 {
  let s2 = self.0[0] * 48271L % 2147483647L
  self.0[0] = s2
  if bound <= 0L {
    0L
  } else {
    s2 % bound
  }
}

///|
/// Join string array with separator.
pub fn join_str(parts : Array[String], sep : String) -> String {
  let sb = StringBuilder()
  let mut i = 0
  while i < parts.length() {
    if i > 0 {
      sb.write_string(sep)
    }
    sb.write_string(parts[i])
    i = i + 1
  }
  sb.to_string()
}

///|
/// Format a Double with fixed 6 decimals (for reproducible reports).
pub fn fmt6(x : Double) -> String {
  let neg = x < 0.0
  let a = if neg { -x } else { x }
  let scaled = (a * 1000000.0).to_int64()
  let int_part = scaled / 1000000L
  let frac = scaled % 1000000L
  let mut frac_s = "\{frac}"
  let mut pad = 6 - frac_s.length()
  while pad > 0 {
    frac_s = "0\{frac_s}"
    pad = pad - 1
  }
  if neg {
    "-\{int_part}.\{frac_s}"
  } else {
    "\{int_part}.\{frac_s}"
  }
}
