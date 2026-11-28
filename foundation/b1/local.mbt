///|
/// local.mbt — 局部域 (local fields)：p 進數 Q_p（有限精度）、賦值、絕對值、Hensel 引理
///
/// Theorem engine:
///   T2 (超度量不等式): |x+y|_p ≤ max(|x|_p, |y|_p)
///   T3 (Hensel 引理): 若 a 是 mod p 二次剩餘，則存在唯一 p 進平方根（牛頓迭代）
///   T4 (局部乘法性): |xy|_p = |x|_p |y|_p

///|
/// A p-adic number with working precision p^prec:
/// value ≡ digits (mod p^prec), and x = p^val · u exactly in Q_p where
/// digits = u·p^val mod p^prec, 0 ≤ digits < p^prec.
pub(all) struct PAdic {
  p : Int64
  prec : Int32
  val : Int32
  digits : Int64
}

///|
/// p^prec as modulus.
pub fn PAdic::modulus(self : PAdic) -> Int64 {
  pow64(self.p, self.prec)
}

///|
/// Construct the p-adic zero at (p, prec).
pub fn PAdic::zero(p : Int64, prec : Int32) -> PAdic {
  PAdic::{ p, prec, val: prec, digits: 0L, }
}

///|
/// Normalize (val, digits): strip trailing p-powers from digits.
fn PAdic::normalize(self : PAdic) -> PAdic {
  let mod = self.modulus()
  let mut d = self.digits % mod
  if d < 0L {
    d = d + mod
  }
  let mut v = self.val
  if d == 0L {
    return PAdic::{ p: self.p, prec: self.prec, val: self.prec, digits: 0L, }
  }
  while v < self.prec && d % self.p == 0L {
    d = d / self.p
    v = v + 1
  }
  PAdic::{ p: self.p, prec: self.prec, val: v, digits: d, }
}

///|
/// Construct from a rational integer n.
pub fn PAdic::from_int(n : Int64, p : Int64, prec : Int32) -> PAdic {
  let x = PAdic::{ p, prec, val: 0, digits: n, }
  x.normalize()
}

///|
/// Construct from a rational number num/den (den not divisible by p required
/// for full precision; works generally with reduced precision otherwise).
pub fn PAdic::from_rat(r : Rat, p : Int64, prec : Int32) -> PAdic {
  let mod = pow64(p, prec)
  // count valuations
  let mut num = r.0
  let mut den = r.1
  let mut v = 0
  while num % p == 0L {
    num = num / p
    v = v + 1
  }
  while den % p == 0L {
    den = den / p
    v = v - 1
  }
  let d = (num % mod + mod) % mod
  let inv_d = mod_inverse((den % mod + mod) % mod, mod)
  if inv_d == 0L {
    abort("PAdic::from_rat: denominator divisible by p")
  }
  let digits = mul_mod64(d, inv_d, mod)
  PAdic::{ p, prec, val: v, digits, }.normalize()
}

///|
/// p-adic absolute value |x|_p = p^{-val} (with |0| = 0).
pub fn PAdic::abs(self : PAdic) -> Double {
  if self.digits == 0L && self.val >= self.prec {
    0.0
  } else {
    let av = if self.val < 0 { -self.val } else { self.val }
    let pw = pow64(self.p, av).to_double()
    if self.val <= 0 {
      pw
    } else {
      1.0 / pw
    }
  }
}

///|
/// Valuation v_p(x).
pub fn PAdic::valuation(self : PAdic) -> Int32 {
  self.val
}

///|
/// p-adic addition (mod p^prec).
pub fn PAdic::add(self : PAdic, other : PAdic) -> PAdic {
  let mod = self.modulus()
  let a = self.digits
  let b = other.digits
  let s = ((a + b) % mod + mod) % mod
  PAdic::{ p: self.p, prec: self.prec, val: 0, digits: s, }.normalize()
}

///|
/// p-adic negation.
pub fn PAdic::neg(self : PAdic) -> PAdic {
  let mod = self.modulus()
  let d = if self.digits == 0L { 0L } else { (mod - self.digits % mod) % mod }
  PAdic::{ p: self.p, prec: self.prec, val: self.val, digits: d, }.normalize()
}

///|
/// p-adic subtraction.
pub fn PAdic::sub(self : PAdic, other : PAdic) -> PAdic {
  self.add(other.neg())
}

///|
/// p-adic multiplication.
pub fn PAdic::mul(self : PAdic, other : PAdic) -> PAdic {
  let mod = self.modulus()
  let d = mul_mod64(self.digits, other.digits, mod)
  PAdic::{ p: self.p, prec: self.prec, val: self.val + other.val, digits: d, }.normalize()
}

///|
/// Whether x is a p-adic unit (val = 0 and nonzero).
pub fn PAdic::is_unit(self : PAdic) -> Bool {
  self.val == 0 && self.digits != 0L
}

///|
/// Whether x is zero (as a truncated p-adic).
pub fn PAdic::is_zero(self : PAdic) -> Bool {
  self.digits == 0L && self.val >= self.prec
}

///|
/// p-adic inverse (for x ≠ 0).
pub fn PAdic::inv(self : PAdic) -> PAdic {
  if self.digits == 0L && self.val >= self.prec {
    abort("PAdic::inv: zero")
  }
  let mod = self.modulus()
  let inv_d = mod_inverse(self.digits, mod)
  if inv_d == 0L {
    abort("PAdic::inv: digits not invertible")
  }
  PAdic::{ p: self.p, prec: self.prec, val: -self.val, digits: inv_d, }.normalize()
}

///|
/// p-adic division.
pub fn PAdic::div(self : PAdic, other : PAdic) -> PAdic {
  self.mul(other.inv())
}

///|
/// p-adic equality (same value mod p^prec after normalization).
pub fn PAdic::equals(self : PAdic, other : PAdic) -> Bool {
  let a = self.normalize()
  let b = other.normalize()
  a.val == b.val && a.digits == b.digits
}

///|
pub fn PAdic::to_string(self : PAdic) -> String {
  if self.digits == 0L && self.val >= self.prec {
    "0"
  } else {
    "\{self.digits}·\{self.p}^\{self.val} (mod \{self.p}^\{self.prec})"
  }
}

///|
/// Integer square root mod p (odd prime p) by brute force. Returns -1 if none.
fn sqrt_mod_p(a : Int64, p : Int64) -> Int64 {
  let mut aa = a % p
  if aa < 0L {
    aa = aa + p
  }
  let mut x = 0L
  while x < p {
    if x * x % p == aa {
      return x
    }
    x = x + 1
  }
  -1L
}

///|
/// Hensel lifting: square root of a unit in Z_p (p odd), given that a is a
/// quadratic residue mod p. Newton iteration x ← (x + a·x^{-1})/2 doubles the
/// correct digits each step. Returns the root x with x² ≡ a (mod p^prec).
/// Theorem T3: such x exists and is unique up to sign in Z_p^×.
pub fn hensel_sqrt(a : PAdic) -> PAdic {
  let p = a.p
  if p == 2L {
    abort("hensel_sqrt: p = 2 not supported")
  }
  if !a.is_unit() {
    abort("hensel_sqrt: need a p-adic unit")
  }
  let mod = a.modulus()
  let x = sqrt_mod_p(a.digits, p)
  if x < 0L {
    abort("hensel_sqrt: a is not a QR mod p")
  }
  // Newton iteration modulo p^prec: x_{n+1} = (x_n + a·x_n^{-1}) / 2
  let mut cur = x
  let mut working_prec = 1
  while working_prec < a.prec {
    working_prec = working_prec * 2
    if working_prec > a.prec {
      working_prec = a.prec
    }
    let m = pow64(p, working_prec)
    let mut cc = cur % m
    if cc < 0L {
      cc = cc + m
    }
    let inv_x = mod_inverse(cc, m)
    let mut aa = a.digits % m
    if aa < 0L {
      aa = aa + m
    }
    let inv2 = mod_inverse(2L, m)
    let t = add_mod64(cc, mul_mod64(aa, inv_x, m), m)
    cur = mul_mod64(t, inv2, m)
  }
  let res = PAdic::{ p, prec: a.prec, val: 0, digits: cur % mod, }
  res.normalize()
}

///|
/// Check the ultrametric inequality for p-adic values x, y.
pub fn ultrametric_ok(x : PAdic, y : PAdic) -> Bool {
  let s = x.add(y)
  let lhs = s.abs()
  let m = x.abs()
  let n = y.abs()
  let mx = if m > n { m } else { n }
  lhs <= mx + 0.000000000001
}

///|
/// Check multiplicativity |xy| = |x|·|y| approximately.
pub fn multiplicativity_ok(x : PAdic, y : PAdic) -> Bool {
  let lhs = x.mul(y).abs()
  let rhs = x.abs() * y.abs()
  let diff = if lhs > rhs { lhs - rhs } else { rhs - lhs }
  diff < 0.000000001
}
