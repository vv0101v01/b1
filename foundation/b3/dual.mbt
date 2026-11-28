///|
/// dual.mbt — 101. 朗蘭茲C-群（Langlands dual group / L-group）
///
/// Root datum (X^*, Φ, X_*, Φ^∨) duality swaps X^* ↔ X_*, Φ ↔ Φ^∨.
/// Concrete: Cartan-matrix model with symmetrizer (long/short data) and
/// fundamental-group / center orders.
///
/// Theorem engine:
///   T101a (對偶對合): ^(^G) = G（Cartan 轉置兩次、π₁ ↔ Z 交換復原）
///   T101b (π₁ ↔ 中心): |π₁(G)| = |Z(G^∨)|（SL₂↔PGL₂、SL₃↔PGL₃ 表）
///   T101c (長短根互換): B₂ ↔ C₂：對稱化子 (2,1) ↔ (1,2)
///   T101d (外爾群): 由反射矩陣生成閉包 |W(A₂)| = 6、|W(B₂)| = 8

///|
/// Root datum in Cartan form.
pub(all) struct RootDatum {
  name : String
  rank : Int32
  cartan : Array[Array[Int32]] // A[i][j] = ⟨α_i^∨, α_j⟩
  symm : Array[Int32] // symmetrizer d_i > 0: d_i·A[i][j] = d_j·A[j][i]
  pi1 : Int32 // |π₁(G)|; −1 = infinite (e.g. G_m)
  center : Int32 // |Z(G)|; −1 = infinite
}

///|
/// Matrix transpose.
pub fn transpose(m : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let n = m.length()
  let res : Array[Array[Int32]] = []
  let mut i = 0
  while i < n {
    let row : Array[Int32] = []
    let mut j = 0
    while j < n {
      row.push(m[j][i])
      j = j + 1
    }
    res.push(row)
    i = i + 1
  }
  res
}

///|
/// Langlands dual root datum.
pub fn RootDatum::dual(self : RootDatum) -> RootDatum {
  RootDatum::{
    name: "dual(" + self.name + ")",
    rank: self.rank,
    cartan: transpose(self.cartan),
    symm: swap_symm(self.symm),
    pi1: self.center,
    center: self.pi1,
  }
}

///|
/// Symmetrizer for the dual: long ↔ short (d'_i = M/d_i, M = lcm-scaling).
fn swap_symm(d : Array[Int32]) -> Array[Int32] {
  // d_i·A_ij = d_j·A_ji symmetric matrix D·A; dual needs D'·A^T symmetric
  // with lengths swapped: d'_i = C/d_i for constant C = product-ish; for
  // rank ≤ 2 use C = d_0·d_1 / gcd-based: just use C = d[0]*d[1] for r = 2
  // and C = d_i-normalized general: d'_i = (prod d)/d_i
  let n = d.length()
  let mut prod = 1
  let mut i = 0
  while i < n {
    prod = prod * d[i]
    i = i + 1
  }
  let res : Array[Int32] = []
  let mut j = 0
  while j < n {
    res.push(prod / d[j])
    j = j + 1
  }
  res
}

///|
/// Symmetrizer validity: d_i·A[i][j] == d_j·A[j][i] for all i, j.
pub fn RootDatum::symmetrizable(self : RootDatum) -> Bool {
  let n = self.rank
  let mut i = 0
  while i < n {
    let mut j = 0
    while j < n {
      if self.symm[i] * self.cartan[i][j] != self.symm[j] * self.cartan[j][i] {
        return false
      }
      j = j + 1
    }
    i = i + 1
  }
  true
}

///|
/// A₁ = SL₂ (simply connected): cartan (2), π₁ = 1, Z = 2 (μ₂).
pub fn root_datum_A1_sc() -> RootDatum {
  RootDatum::{
    name: "SL2",
    rank: 1,
    cartan: [[2]],
    symm: [1],
    pi1: 1,
    center: 2,
  }
}

///|
/// A₁ adjoint = PGL₂: π₁ = 2, Z = 1.
pub fn root_datum_A1_ad() -> RootDatum {
  RootDatum::{
    name: "PGL2",
    rank: 1,
    cartan: [[2]],
    symm: [1],
    pi1: 2,
    center: 1,
  }
}

///|
/// A₂ simply connected = SL₃: π₁ = 1, Z = 3.
pub fn root_datum_A2_sc() -> RootDatum {
  RootDatum::{
    name: "SL3",
    rank: 2,
    cartan: [[2, -1], [-1, 2]],
    symm: [1, 1],
    pi1: 1,
    center: 3,
  }
}

///|
/// B₂: cartan [[2,-1],[-2,2]], symm (2, 1).
pub fn root_datum_B2() -> RootDatum {
  RootDatum::{
    name: "B2",
    rank: 2,
    cartan: [[2, -1], [-2, 2]],
    symm: [2, 1],
    pi1: 1,
    center: 2,
  }
}

///|
/// C₂: cartan [[2,-2],[-1,2]], symm (1, 2).
pub fn root_datum_C2() -> RootDatum {
  RootDatum::{
    name: "C2",
    rank: 2,
    cartan: [[2, -2], [-1, 2]],
    symm: [1, 2],
    pi1: 1,
    center: 2,
  }
}

///|
pub fn mat_mul(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let n = a.length()
  let res : Array[Array[Int32]] = []
  let mut i = 0
  while i < n {
    let row : Array[Int32] = []
    let mut j = 0
    while j < n {
      let mut s = 0
      let mut k = 0
      while k < n {
        s = s + a[i][k] * b[k][j]
        k = k + 1
      }
      row.push(s)
      j = j + 1
    }
    res.push(row)
    i = i + 1
  }
  res
}

///|
fn mat_eq(a : Array[Array[Int32]], b : Array[Array[Int32]]) -> Bool {
  let mut i = 0
  while i < a.length() {
    let mut j = 0
    while j < a.length() {
      if a[i][j] != b[i][j] {
        return false
      }
      j = j + 1
    }
    i = i + 1
  }
  true
}

///|
/// Simple reflection s_i on the root lattice: s_i(e_j) = e_j − A[i][j]·e_i.
fn simple_reflection(a : Array[Array[Int32]], i : Int32) -> Array[Array[Int32]] {
  let n = a.length()
  let res : Array[Array[Int32]] = []
  let mut r = 0
  while r < n {
    let row : Array[Int32] = []
    let mut c = 0
    while c < n {
      let v = if r == c { 1 } else { 0 }
      let w = if r == i { a[i][c] } else { 0 }
      row.push(v - w)
      c = c + 1
    }
    res.push(row)
    r = r + 1
  }
  res
}

///|
/// Generate the Weyl group as matrices (BFS closure). Returns group order.
pub fn weyl_group_order(datum : RootDatum) -> Int32 {
  let n = datum.rank
  let gens : Array[Array[Array[Int32]]] = []
  let mut i = 0
  while i < n {
    gens.push(simple_reflection(datum.cartan, i))
    i = i + 1
  }
  // identity
  let idm : Array[Array[Int32]] = []
  let mut r = 0
  while r < n {
    let row : Array[Int32] = []
    let mut c = 0
    while c < n {
      row.push(if r == c { 1 } else { 0 })
      c = c + 1
    }
    idm.push(row)
    r = r + 1
  }
  let group : Array[Array[Array[Int32]]] = []
  group.push(idm)
  let mut changed = true
  while changed {
    changed = false
    let snapshot = group.length()
    let mut gi = 0
    while gi < snapshot {
      let mut gj = 0
      while gj < gens.length() {
        let prod = mat_mul(gens[gj], group[gi])
        let mut seen = false
        let mut k = 0
        while k < group.length() {
          if mat_eq(group[k], prod) {
            seen = true
          }
          k = k + 1
        }
        if !seen {
          group.push(prod)
          changed = true
        }
        gj = gj + 1
      }
      gi = gi + 1
    }
  }
  group.length()
}
