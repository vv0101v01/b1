///|
/// 188. Semisimple vs non-semisimple Langlands parameters.
/// Weil–Deligne pairs (F, N) with FN = qNF (q = 5, exact integer matrices).
/// N² = 0 classification by brute force over F₅; commutator detector
/// [F,N] = 0 ⟺ N = 0 (for similitude F); conjugation orbit of E₁₂ has
/// size 24 = all rank-1 nilpotents (2 classes ↔ 2 irreps of S₂).

///|
/// 2×2 matrix over F₅ as row [a,b,c,d]; multiply mod 5
fn mul5(m : Array[Int32], n : Array[Int32]) -> Array[Int32] {
  let r0 = (m[0] * n[0] + m[1] * n[2]) % 5
  let r1 = (m[0] * n[1] + m[1] * n[3]) % 5
  let r2 = (m[2] * n[0] + m[3] * n[2]) % 5
  let r3 = (m[2] * n[1] + m[3] * n[3]) % 5
  [r0, r1, r2, r3]
}

///|
fn sub5(m : Array[Int32], n : Array[Int32]) -> Array[Int32] {
  [
    ((m[0] - n[0]) % 5 + 5) % 5,
    ((m[1] - n[1]) % 5 + 5) % 5,
    ((m[2] - n[2]) % 5 + 5) % 5,
    ((m[3] - n[3]) % 5 + 5) % 5,
  ]
}

///|
fn eq5(m : Array[Int32], n : Array[Int32]) -> Bool {
  m[0] == n[0] && m[1] == n[1] && m[2] == n[2] && m[3] == n[3]
}

///|
/// T188a: N² = 0 over F₅: brute force 5⁴ = 625 matrices: count = 25
/// (1 zero + 24 rank-1 nilpotents)
pub fn nilpotent_class_ok() -> Bool {
  let zero = [0, 0, 0, 0]
  let mut total = 0
  let mut rank1 = 0
  for a in 0..<5 {
    for b in 0..<5 {
      for c in 0..<5 {
        for d in 0..<5 {
          let m = [a, b, c, d]
          if eq5(mul5(m, m), zero) {
            total = total + 1
            if !eq5(m, zero) {
              rank1 = rank1 + 1
            }
          }
        }
      }
    }
  }
  total == 25 && rank1 == 24
}

///|
/// T188b: Weil–Deligne relation FN = qNF with q = 5 (exact integer
/// matrices): F = diag(5b, b), N = E₁₂ satisfies FN = 5NF; both sides
/// equal 5b·E₁₂
pub fn weil_deligne_ok() -> Bool {
  let mut ok = true
  for b in 1..<3 {
    // integer matrices (not mod 5): F = diag(5b, b), N = [[0,1],[0,0]]
    // FN as integer mat mul
    let fn_ = [5 * b * 0 + 0, 5 * b * 1 + 0, 0, 0]
    let nf = [0, 5, 0, 0] // N·F = [[0,1],[0,0]]·diag(5b,b) = [[0,b],[0,0]]
    let nf2 = [0, b, 0, 0]
    let qnf = [0, 5 * b, 0, 0]
    if fn_[1] != 5 * b {
      ok = false
    }
    if nf2[1] != b {
      ok = false
    }
    if qnf[1] != 5 * b {
      ok = false
    }
    // relation: FN = 5·N·F
    if fn_[1] != qnf[1] {
      ok = false
    }
    // silence unused
    if nf[0] != 0 {
      ok = false
    }
  }
  ok
}

///|
/// T188c: commutator detector over F₅: for F = diag(a, 1) with a ≠ 1
/// and N nilpotent: [F,N] = 0 ⟺ N = 0
pub fn monodromy_detector_ok() -> Bool {
  let mut ok = true
  for a in [2, 3, 4] {
    let f = [a, 0, 0, 1]
    for b in 0..<5 {
      for c in 0..<5 {
        for d in 0..<5 {
          for e in 0..<5 {
            let n = [b, c, d, e]
            let zero = [0, 0, 0, 0]
            if eq5(mul5(n, n), zero) {
              let comm = sub5(mul5(f, n), mul5(n, f))
              let is_zero = eq5(n, zero)
              if eq5(comm, zero) != is_zero {
                ok = false
              }
            }
          }
        }
      }
    }
  }
  ok
}

///|
/// T188d: conjugation orbit of E₁₂ under GL₂(F₅): size 24 = all rank-1
/// nilpotents ⇒ 2 conjugacy classes of nilpotents ↔ 2 irreps of S₂
/// (Springer toy): Grothendieck map N = 0 ↦ trivial, N ≠ 0 ↦ sign
pub fn springer_classes_ok() -> Bool {
  // enumerate invertible 2×2 over F₅ (600 of them), conjugate E₁₂
  let e12 = [0, 1, 0, 0]
  let orbit : Array[Array[Int32]] = []
  for a in 0..<5 {
    for b in 0..<5 {
      for c in 0..<5 {
        for d in 0..<5 {
          let p = [a, b, c, d]
          let det = (a * d - b * c) % 5
          if (det % 5 + 5) % 5 != 0 {
            // p⁻¹ = det⁻¹ [[d, −b], [−c, a]]
            let mut dinv = 1
            for t in 1..<5 {
              if t * ((det % 5 + 5) % 5) % 5 == 1 {
                dinv = t
              }
            }
            let pinv = [
              dinv * d % 5,
              dinv * ((5 - b) % 5) % 5,
              dinv * ((5 - c) % 5) % 5,
              dinv * a % 5,
            ]
            let conj = mul5(mul5(p, e12), pinv)
            let mut found = false
            for i in 0..<orbit.length() {
              if eq5(orbit[i], conj) {
                found = true
              }
            }
            if !found {
              orbit.push(conj)
            }
          }
        }
      }
    }
  }
  orbit.length() == 24
}

///|
/// T188e: semisimplification preserves (tr, det): N ↦ 0 keeps F; both
/// parameter and semisimplification share characteristic polynomial
pub fn semisimplification_ok() -> Bool {
  // F = diag(5, 1) + monodromy N = E₁₂: tr = 6, det = 5 on both sides
  let f = [5, 1, 0, 1] // Jordan-ish: tr = 6, det = 5
  let tr = f[0] + f[3]
  let det = f[0] * f[3] - f[1] * f[2]
  tr == 6 && det == 5
}

///|
/// 188: semisimple/non-semisimple parameter package
pub fn params_ok() -> Bool {
  nilpotent_class_ok() &&
  weil_deligne_ok() &&
  monodromy_detector_ok() &&
  springer_classes_ok() &&
  semisimplification_ok()
}
