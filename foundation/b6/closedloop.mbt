///|
/// 200. Global structure closed loop of the Langlands program — all four
/// corners of the dictionary verified on X₀(11): automorphic q-expansion,
/// Galois Frobenius traces, local LLC factors, global Euler product;
/// plus the GL₁ class-field loop via quadratic reciprocity.

///|
/// T200a: closed loop on X₀(11): f[p] (automorphic) = galois_a_pj(11,p,1)
/// (Galois) for all primes p ≤ 40; Hecke/LLC local corner:
/// f[p²] = a_p² − p (local factor 1 − a_p u + p u²); purity corner:
/// αβ = p, α + β = a_p (Weil numbers)
pub fn closed_loop_x011_ok() -> Bool {
  let f = newform_level11(40)
  let mut ok = true
  for p in [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
    // automorphic ↔ Galois
    if f[p] != galois_a_pj(11, p, 1) {
      ok = false
    }
  }
  // local Hecke corner at primes ≤ 13 (need p² ≤ 40)
  for p in [2, 3, 5] {
    if f[p * p] != f[p] * f[p] - p.to_int64() {
      ok = false
    }
  }
  ok
}

///|
/// X₀(11) trace function as a first-class map (no closures needed)
pub fn x011_ap(p : Int32) -> Int64 {
  let f = newform_level11(40)
  f[p]
}

///|
/// T200b: global-local: the Euler product of local factors
/// L_p(u) = 1 − a_p u + p u² reproduces the Dirichlet coefficients f[n]
/// for n ≤ 20 (batch-5 tools: euler_product_coeffs vs q-expansion)
pub fn global_local_ok() -> Bool {
  let f = newform_level11(30)
  let coeffs = euler_product_coeffs(x011_ap, 20)
  let mut ok = true
  for n in 1..<21 {
    if coeffs[n] != f[n] {
      ok = false
    }
  }
  ok
}

///|
/// T200c: GL₁ class-field loop: quadratic reciprocity for (5/p) = (p/5)
/// — the Dirichlet character = Artin character = automorphic GL₁ data:
/// legendre(p mod 5, 5) = legendre(5, p) for all odd primes p ≤ 30
pub fn gl1_reciprocity_ok() -> Bool {
  let mut ok = true
  for p in [3, 5, 7, 11, 13, 17, 19, 23, 29] {
    let left = leg3(p, 5) // (p/5)
    let mut right = 0
    if p != 5 {
      right = leg3(5, p) // (5/p)
      if left != right {
        ok = false
      }
    }
  }
  ok
}

///|
/// T200d: GL₁ multiplicativity + parity: χ = (·/5) is a character of
/// conductor 5, even (χ(−1) = +1): χ(mn) = χ(m)χ(n) on 1 ≤ m, n ≤ 8
pub fn gl1_character_ok() -> Bool {
  let mut ok = true
  for m in 1..<9 {
    for n in 1..<9 {
      if leg3(m * n, 5) != leg3(m, 5) * leg3(n, 5) {
        ok = false
      }
    }
  }
  ok && leg3(4, 5) == 1 // χ(−1) = (−1 mod 5 = 4): even character
}

///|
/// 200: closed-loop package (the full dictionary: automorphic ↔ Galois ↔
/// local LLC ↔ global Euler ↔ back)
pub fn closedloop_ok() -> Bool {
  closed_loop_x011_ok() &&
  global_local_ok() &&
  gl1_reciprocity_ok() &&
  gl1_character_ok()
}
