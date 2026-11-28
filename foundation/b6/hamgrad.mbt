///|
/// 193. Graded Hamiltonian spaces — polynomial Poisson algebra on
/// (q₁, q₂, p₁, p₂) with {q_i, p_j} = δ_ij; degree ≤ 2 polynomials on a
/// 15-monomial basis; the Euclidean algebra e(2) comoment is a Lie
/// morphism; weight grading wt(q) = 1, wt(p) = −1 is preserved.

///|
/// basis of monomials of degree ≤ 2 in (q1, q2, p1, p2): index order
/// 0: 1; 1..4: q1, q2, p1, p2; 5..14: q1², q1q2, q1p1, q1p2, q2²,
/// q2p1, q2p2, p1², p1p2, p2²
pub fn mono_index(e : (Int32, Int32, Int32, Int32)) -> Int32 {
  let (a, b, c, d) = e
  let s = a + b + c + d
  if s == 0 {
    return 0
  }
  if s == 1 {
    if a == 1 {
      return 1
    }
    if b == 1 {
      return 2
    }
    if c == 1 {
      return 3
    }
    return 4
  }
  // s = 2
  if a == 2 {
    return 5
  }
  if a == 1 && b == 1 {
    return 6
  }
  if a == 1 && c == 1 {
    return 7
  }
  if a == 1 && d == 1 {
    return 8
  }
  if b == 2 {
    return 9
  }
  if b == 1 && c == 1 {
    return 10
  }
  if b == 1 && d == 1 {
    return 11
  }
  if c == 2 {
    return 12
  }
  if c == 1 && d == 1 {
    return 13
  }
  14
}

///|
/// product of two degree ≤ 1 monomials as a basis index of degree ≤ 2
/// (returns -1 for the constant×· cases handled by index 0 identity)
pub fn mul_basis(i : Int32, j : Int32) -> Int32 {
  if i == 0 {
    return j
  }
  if j == 0 {
    return i
  }
  // both degree 1: exponents sum to degree 2
  let e1 = basis_exp(i)
  let e2 = basis_exp(j)
  mono_index((e1.0 + e2.0, e1.1 + e2.1, e1.2 + e2.2, e1.3 + e2.3))
}

///|
fn basis_exp(i : Int32) -> (Int32, Int32, Int32, Int32) {
  if i == 1 {
    (1, 0, 0, 0)
  } else if i == 2 {
    (0, 1, 0, 0)
  } else if i == 3 {
    (0, 0, 1, 0)
  } else if i == 4 {
    (0, 0, 0, 1)
  } else {
    (0, 0, 0, 0)
  }
}

///|
/// Poisson bracket on basis monomials: {m_i, m_j} = Σ_k (∂q_k i · ∂p_k j −
/// ∂p_k i · ∂q_k j); result as 15-dim coefficient vector
pub fn bracket_basis(i : Int32, j : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for _k in 0..<15 {
    out.push(0)
  }
  // derivative of basis monomial wrt variable v = (q1:0, q2:1, p1:2, p2:3)
  // returns (coefficient, basis-index-of-derivative)
  let mut acc_k = 0
  while acc_k < 2 {
    // q_{k+1} vs p_{k+1}: k = 0 → q1/p1, k = 1 → q2/p2
    let qi = if acc_k == 0 { 1 } else { 2 }
    let pi = if acc_k == 0 { 3 } else { 4 }
    let dq_i = deriv(i, qi)
    let dp_j = deriv(j, pi)
    let dp_i = deriv(i, pi)
    let dq_j = deriv(j, qi)
    // term 1: ∂q i · ∂p j
    if dq_i.0 != 0 && dp_j.0 != 0 {
      let idx = mul_basis(dq_i.1, dp_j.1)
      out[idx] = out[idx] + dq_i.0 * dp_j.0
    }
    // term 2: − ∂p i · ∂q j
    if dp_i.0 != 0 && dq_j.0 != 0 {
      let idx = mul_basis(dp_i.1, dq_j.1)
      out[idx] = out[idx] - dp_i.0 * dq_j.0
    }
    acc_k = acc_k + 1
  }
  out
}

///|
/// derivative of basis monomial i (degree ≤ 2) wrt variable v:
/// (coefficient, basis index) with (0, 0) for zero
pub fn deriv(i : Int32, v : Int32) -> (Int32, Int32) {
  if i == 0 {
    return (0, 0)
  }
  let e = basis_exp_of(i)
  let exp = if v == 1 {
    e.0
  } else if v == 2 {
    e.1
  } else if v == 3 {
    e.2
  } else {
    e.3
  }
  if exp == 0 {
    return (0, 0)
  }
  // variable letter index v: 1..4
  let mut new_e = e
  if v == 1 {
    new_e = (e.0 - 1, e.1, e.2, e.3)
  } else if v == 2 {
    new_e = (e.0, e.1 - 1, e.2, e.3)
  } else if v == 3 {
    new_e = (e.0, e.1, e.2 - 1, e.3)
  } else {
    new_e = (e.0, e.1, e.2, e.3 - 1)
  }
  (exp, mono_index(new_e))
}

///|
fn basis_exp_of(i : Int32) -> (Int32, Int32, Int32, Int32) {
  if i == 0 {
    (0, 0, 0, 0)
  } else if i == 1 {
    (1, 0, 0, 0)
  } else if i == 2 {
    (0, 1, 0, 0)
  } else if i == 3 {
    (0, 0, 1, 0)
  } else if i == 4 {
    (0, 0, 0, 1)
  } else if i == 5 {
    (2, 0, 0, 0)
  } else if i == 6 {
    (1, 1, 0, 0)
  } else if i == 7 {
    (1, 0, 1, 0)
  } else if i == 8 {
    (1, 0, 0, 1)
  } else if i == 9 {
    (0, 2, 0, 0)
  } else if i == 10 {
    (0, 1, 1, 0)
  } else if i == 11 {
    (0, 1, 0, 1)
  } else if i == 12 {
    (0, 0, 2, 0)
  } else if i == 13 {
    (0, 0, 1, 1)
  } else {
    (0, 0, 0, 2)
  }
}

///|
/// T193a: the Euclidean comoment is a Lie morphism (exact 15-dim vectors):
/// μ_x = p₁ (index 3), μ_y = p₂ (index 4), μ_J = q₁p₂ − q₂p₁ (index 8 − 10):
/// {μ_J, μ_x} = μ_y; {μ_J, μ_y} = −μ_x; {μ_x, μ_y} = 0
pub fn comoment_lie_ok() -> Bool {
  let mu_x : Array[Int32] = []
  let mu_y : Array[Int32] = []
  let mu_j : Array[Int32] = []
  for _k in 0..<15 {
    mu_x.push(0)
    mu_y.push(0)
    mu_j.push(0)
  }
  mu_x[3] = 1
  mu_y[4] = 1
  mu_j[8] = 1
  mu_j[10] = -1
  let jx = bracket_vec(mu_j, mu_x)
  let jy = bracket_vec(mu_j, mu_y)
  let xy = bracket_vec(mu_x, mu_y)
  // {μ_J, μ_x} = μ_y : coefficient check
  let mut ok = true
  for k in 0..<15 {
    if jx[k] != mu_y[k] {
      ok = false
    }
    if jy[k] != -mu_x[k] {
      ok = false
    }
    if xy[k] != 0 {
      ok = false
    }
  }
  ok
}

///|
/// bracket of two general polys (15-dim coefficient vectors)
pub fn bracket_vec(f : Array[Int32], g : Array[Int32]) -> Array[Int32] {
  let out : Array[Int32] = []
  for _k in 0..<15 {
    out.push(0)
  }
  for i in 0..<15 {
    if f[i] != 0 {
      for j in 0..<15 {
        if g[j] != 0 {
          let b = bracket_basis(i, j)
          for k in 0..<15 {
            out[k] = out[k] + f[i] * g[j] * b[k]
          }
        }
      }
    }
  }
  out
}

///|
/// T193b: Jacobi on basis degree ≤ 2: {i,{j,k}} + cyclic = 0
/// (15³ = 3375 triples, exact)
pub fn jacobi_poly_ok() -> Bool {
  let mut ok = true
  for i in 0..<15 {
    for j in 0..<15 {
      for k in 0..<15 {
        let f : Array[Int32] = []
        let g : Array[Int32] = []
        let h : Array[Int32] = []
        for _t in 0..<15 {
          f.push(0)
          g.push(0)
          h.push(0)
        }
        f[i] = 1
        g[j] = 1
        h[k] = 1
        let gh = bracket_vec(g, h)
        let hf = bracket_vec(h, f)
        let fg = bracket_vec(f, g)
        let t1 = bracket_vec(f, gh)
        let t2 = bracket_vec(g, hf)
        let t3 = bracket_vec(h, fg)
        for m in 0..<15 {
          if t1[m] + t2[m] + t3[m] != 0 {
            ok = false
          }
        }
      }
    }
  }
  ok
}

///|
/// T193c: weight grading: wt(q_i) = 1, wt(p_i) = −1; the bracket
/// {·,·} preserves total weight; μ_J = q₁p₂ − q₂p₁ has weight 0
pub fn weight_grading_ok() -> Bool {
  // wt of basis monomial = a − b·? exponents (q1^a q2^b p1^c p2^d):
  // wt = (a + b) − (c + d)
  let mut ok = true
  for i in 0..<15 {
    for j in 0..<15 {
      let wi = weight_of(i)
      let wj = weight_of(j)
      let b = bracket_basis(i, j)
      for k in 0..<15 {
        if b[k] != 0 {
          if weight_of(k) != wi + wj {
            ok = false
          }
        }
      }
    }
  }
  ok
}

///|
fn weight_of(i : Int32) -> Int32 {
  let e = basis_exp_of(i)
  e.0 + e.1 - e.2 - e.3
}

///|
/// 193: graded Hamiltonian package
pub fn hamgrad_ok() -> Bool {
  comoment_lie_ok() && jacobi_poly_ok() && weight_grading_ok()
}
