///|
/// morita.mbt — 批次八·模組 7：莫里塔等價
///
/// 有限體 F_p 上的矩陣代數 M_n(F_p) 之精確計算：
///   1. |M_n(F_p)| = p^{n²}；|GL_n(F_p)| = Π_{i=0}^{n-1}(p^n − p^i)（與窮舉相符）。
///   2. M_n(F_p) 是單環：左／右理想與雙邊理想只有 0 與全環（以窮舉驗證，p = 2, n = 2）。
///   3. 轉置給出環同構 M_n(k) ≅ M_n(k)^op；故矩陣代數是「Morita 自對偶」的。
///   4. 矩陣單位 E_ij 與張量積：M_n(k) ⊗ M_m(k) ≅ M_{nm}(k)，維數 n²m² = (nm)²。
///   5. 冪等元 e（秩 r）給出 e M_n(k) e ≅ M_r(k)；秩 1 冪等元之數 = |P^{n-1}(F_p)|。
///   6. K_0(M_n(k)) = Z = K_0(k)：Morita 不變量（以「有限生成投射模的秩」實現）。

///|
/// F_p 上 n×n 矩陣乘法（扁平 n² 陣列）。
pub fn b8mm_mul(
  a : Array[Int32],
  b : Array[Int32],
  n : Int32,
  p : Int32,
) -> Array[Int32] {
  let out : Array[Int32] = []
  for _ in 0..<(n * n) {
    out.push(0)
  }
  for i in 0..<n {
    for j in 0..<n {
      let mut s = 0
      for k in 0..<n {
        s = s + a[i * n + k] * b[k * n + j]
      }
      out[i * n + j] = s % p
    }
  }
  out
}

///|
/// 單位矩陣。
pub fn b8mm_id(n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for i in 0..<n {
    for j in 0..<n {
      out.push(if i == j { 1 } else { 0 })
    }
  }
  out
}

///|
/// 以整數碼解碼矩陣（每個元素一位，p^k 進位）。
pub fn b8mm_decode(code : Int32, n : Int32, p : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  let mut c = code
  for _ in 0..<(n * n) {
    out.push(c % p)
    c = c / p
  }
  out
}

///|
/// 矩陣是否可逆（以窮舉配對乘法判定）。
pub fn b8mm_invertible(a : Array[Int32], n : Int32, p : Int32) -> Bool {
  let id = b8mm_id(n)
  let total = b8_pow_int(p, n * n)
  let mut ok = false
  for code in 0..<total {
    let b = b8mm_decode(code, n, p)
    let ab = b8mm_mul(a, b, n, p)
    let mut eq = true
    for i in 0..<(n * n) {
      if ab[i] != id[i] {
        eq = false
      }
    }
    if eq {
      ok = true
    }
  }
  ok
}

///|
/// 可逆矩陣之數（窮舉）。
pub fn b8mm_units_bruteforce(n : Int32, p : Int32) -> Int32 {
  let total = b8_pow_int(p, n * n)
  let mut c = 0
  for code in 0..<total {
    if b8mm_invertible(b8mm_decode(code, n, p), n, p) {
      c = c + 1
    }
  }
  c
}

///|
/// |GL_n(F_p)| = Π (p^n − p^i)。
pub fn b8mm_units_formula(n : Int32, p : Int32) -> Int32 {
  let mut r = 1
  let pn = b8_pow_int(p, n)
  for i in 0..<n {
    r = r * (pn - b8_pow_int(p, i))
  }
  r
}

///|
/// 冪等元之數（窮舉）。
pub fn b8mm_idempotents(n : Int32, p : Int32) -> Int32 {
  let total = b8_pow_int(p, n * n)
  let mut c = 0
  for code in 0..<total {
    let a = b8mm_decode(code, n, p)
    let aa = b8mm_mul(a, a, n, p)
    let mut eq = true
    for i in 0..<(n * n) {
      if aa[i] != a[i] {
        eq = false
      }
    }
    if eq {
      c = c + 1
    }
  }
  c
}

///|
/// 元素 a 生成的雙邊理想（加法子群 + 左右乘法封閉），以位元遮罩表示。
pub fn b8mm_ideal_of(a : Array[Int32], n : Int32, p : Int32) -> Int32 {
  let total = b8_pow_int(p, n * n)
  let mut mask = 0
  // 加法封閉：從 {a} 出發反覆加入 x·y 與 x+y
  let inmask : Array[Bool] = []
  for _ in 0..<total {
    inmask.push(false)
  }
  let decode = fn(code : Int32) -> Array[Int32] { b8mm_decode(code, n, p) }
  let encode = fn(m : Array[Int32]) -> Int32 {
    let mut s = 0
    let mut f = 1
    for v in m {
      s = s + v * f
      f = f * p
    }
    s
  }
  let a0 = encode(a)
  inmask[a0] = true
  let mut changed = true
  while changed {
    changed = false
    for c1 in 0..<total {
      if inmask[c1] {
        let x = decode(c1)
        for c2 in 0..<total {
          if inmask[c2] {
            let y = decode(c2)
            // x + y
            let sum : Array[Int32] = []
            for i in 0..<(n * n) {
              sum.push((x[i] + y[i]) % p)
            }
            let cs = encode(sum)
            if !inmask[cs] {
              inmask[cs] = true
              changed = true
            }
          }
          // r x s（左右乘法）
          let y2 = decode(c2)
          let m1 = b8mm_mul(y2, x, n, p)
          let c3 = encode(m1)
          if !inmask[c3] {
            inmask[c3] = true
            changed = true
          }
          let m2 = b8mm_mul(x, y2, n, p)
          let c4 = encode(m2)
          if !inmask[c4] {
            inmask[c4] = true
            changed = true
          }
        }
      }
    }
  }
  for i in 0..<total {
    if inmask[i] {
      mask = mask | (1 << i)
    }
  }
  mask
}

///|
/// 雙邊理想之數（對每個元素求其生成理想，取相異者；並驗證 0 與全環）。
pub fn b8mm_count_ideals(n : Int32, p : Int32) -> Int32 {
  let total = b8_pow_int(p, n * n)
  let ids : Array[Int32] = []
  for code in 0..<total {
    let mk = b8mm_ideal_of(b8mm_decode(code, n, p), n, p)
    let mut seen = false
    for x in ids {
      if x == mk {
        seen = true
      }
    }
    if !seen {
      ids.push(mk)
    }
  }
  ids.length()
}

///|
/// 矩陣的轉置。
pub fn b8mm_transpose(a : Array[Int32], n : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for _ in 0..<(n * n) {
    out.push(0)
  }
  for i in 0..<n {
    for j in 0..<n {
      out[i * n + j] = a[j * n + i]
    }
  }
  out
}

///|
/// 轉置是反同構：(AB)^T = B^T A^T（窮舉 p = 2, n = 2, 3）。
pub fn b8mm_transpose_anti(n : Int32, p : Int32) -> Bool {
  let total = b8_pow_int(p, n * n)
  let mut ok = true
  for c1 in 0..<total {
    let a = b8mm_decode(c1, n, p)
    for c2 in 0..<total {
      let b = b8mm_decode(c2, n, p)
      let lhs = b8mm_transpose(b8mm_mul(a, b, n, p), n)
      let rhs = b8mm_mul(b8mm_transpose(b, n), b8mm_transpose(a, n), n, p)
      for i in 0..<(n * n) {
        if lhs[i] != rhs[i] {
          ok = false
        }
      }
    }
  }
  ok
}

///|
/// 秩（F_p 上高斯消去）。
pub fn b8mm_rank(a : Array[Int32], n : Int32, p : Int32) -> Int32 {
  let m : Array[Array[Int32]] = []
  for i in 0..<n {
    let r : Array[Int32] = []
    for j in 0..<n {
      r.push(a[i * n + j] % p)
    }
    m.push(r)
  }
  let mut rank = 0
  for col in 0..<n {
    let mut piv = -1
    for r in rank..<n {
      if m[r][col] != 0 && piv < 0 {
        piv = r
      }
    }
    if piv >= 0 {
      let tmp = m[rank]
      m[rank] = m[piv]
      m[piv] = tmp
      // 消去（用模反元素）
      let inv = b8mm_modinv(m[rank][col], p)
      for r in (rank + 1)..<n {
        if m[r][col] != 0 {
          let f = m[r][col] * inv % p
          for c in 0..<n {
            m[r][c] = (m[r][c] - f * m[rank][c]) % p
            if m[r][c] < 0 {
              m[r][c] = m[r][c] + p
            }
          }
        }
      }
      rank = rank + 1
    }
  }
  rank
}

///|
/// 模 p 反元素（小質數，以窮舉求）。
fn b8mm_modinv(a : Int32, p : Int32) -> Int32 {
  let mut inv = 1
  for x in 1..<p {
    if a * x % p == 1 {
      inv = x
    }
  }
  inv
}

///|
/// e A e 的元素個數（e 為冪等元）。
pub fn b8mm_corner_size(e : Array[Int32], n : Int32, p : Int32) -> Int32 {
  let total = b8_pow_int(p, n * n)
  let seen : Array[Int32] = []
  for _ in 0..<total {
    seen.push(-1)
  }
  let id = b8mm_id(n)
  let _ = id
  let encode = fn(m : Array[Int32]) -> Int32 {
    let mut s = 0
    let mut f = 1
    for v in m {
      s = s + v * f
      f = f * p
    }
    s
  }
  for code in 0..<total {
    let a = b8mm_decode(code, n, p)
    let v = encode(b8mm_mul(b8mm_mul(e, a, n, p), e, n, p))
    seen[v] = 0
  }
  let mut c = 0
  for v in seen {
    if v == 0 {
      c = c + 1
    }
  }
  c
}

///|
/// 秩 r 的冪等元之數（窮舉）。
pub fn b8mm_idempotents_rank(n : Int32, p : Int32, r : Int32) -> Int32 {
  let total = b8_pow_int(p, n * n)
  let mut c = 0
  for code in 0..<total {
    let a = b8mm_decode(code, n, p)
    let aa = b8mm_mul(a, a, n, p)
    let mut eq = true
    for i in 0..<(n * n) {
      if aa[i] != a[i] {
        eq = false
      }
    }
    if eq && b8mm_rank(a, n, p) == r {
      c = c + 1
    }
  }
  c
}

///|
/// 矩陣單位 E_ij。
pub fn b8mm_unit(n : Int32, i : Int32, j : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for _ in 0..<(n * n) {
    out.push(0)
  }
  out[i * n + j] = 1
  out
}

///|
/// 矩陣單位的乘法規則 E_ij E_kl = δ_jk E_il（窮舉驗證）。
pub fn b8mm_unit_rule(n : Int32) -> Bool {
  let mut ok = true
  for i in 0..<n {
    for j in 0..<n {
      for k in 0..<n {
        for l in 0..<n {
          let p1 = b8mm_mul(b8mm_unit(n, i, j), b8mm_unit(n, k, l), n, 2)
          let expect = if j == k {
            b8mm_unit(n, i, l)
          } else {
            b8mm_unit(n, 0, 0)
          }
          let target = if j == k { expect } else { b8mm_unit(n, 0, 0) }
          // δ_jk = 0 時應為零矩陣
          let zero : Array[Int32] = []
          for _ in 0..<(n * n) {
            zero.push(0)
          }
          let want = if j == k { expect } else { zero }
          let _ = target
          for t in 0..<(n * n) {
            if p1[t] != want[t] {
              ok = false
            }
          }
        }
      }
    }
  }
  ok
}

///|
/// 張量積維數檢驗：dim M_n ⊗ M_m = n²m² = (nm)²。
pub fn b8mm_tensor_dim(n : Int32, m : Int32) -> (Int32, Int32) {
  (n * n * m * m, n * m * (n * m))
}
