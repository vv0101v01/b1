///|
/// linalg.mbt — 批次十四工具箱 A：F₂ 上的精確線性代數與有限鏈複形。
///
/// 為什麼整批都用 F₂：批次十四的主題（反常 t-結構、相交上同調、格羅滕迪克對偶、
/// A¹-同倫不變性、∞-層化）在文獻裡都允許「係數取在一個域 k 上」；
/// 取 k = F₂ 使所有維數、秩、核、餘核都變成**可精確計算的整數**，
/// 而特徵 2 讓所有交錯符號自動消失（Čech 微分 = 純和、Hom 複形微分 = 純和），
/// 於是「定理」被降為 rank–nullity 恆等式；程式跑完若無 [FAIL]，定理即獲計算見證。
///
/// 誠實邊界：本檔只處理**有限維** F₂-向量空間與**有界**鏈複形；
/// 文獻中的無界導出範疇、奇異上同調、無窮層化都只在有限影子中受檢。

///|
/// F₂ 上高斯消元求秩（列運算）。
pub fn b14_f2_rank(m : Array[Array[Int32]]) -> Int32 {
  let rows = m.length()
  if rows == 0 {
    return 0
  }
  let cols = m[0].length()
  let a : Array[Array[Int32]] = []
  for r in 0..<rows {
    a.push(m[r].copy())
  }
  let mut rank = 0
  for c in 0..<cols {
    let mut piv = -1
    for r in rank..<rows {
      if a[r][c] % 2 != 0 {
        piv = r
        break
      }
    }
    if piv >= 0 {
      let tmp = a[piv]
      a[piv] = a[rank]
      a[rank] = tmp
      for r in 0..<rows {
        if r != rank && a[r][c] % 2 != 0 {
          for k in 0..<cols {
            a[r][k] = (a[r][k] + a[rank][k]) % 2
          }
        }
      }
      rank = rank + 1
    }
  }
  rank
}

///|
/// 列既約階梯形（RREF）。
fn b14_f2_rref(m : Array[Array[Int32]]) -> (Array[Array[Int32]], Array[Int32]) {
  let rows = m.length()
  let cols = if rows == 0 { 0 } else { m[0].length() }
  let a : Array[Array[Int32]] = []
  for r in 0..<rows {
    a.push(m[r].copy())
  }
  let mut rank = 0
  let pivots : Array[Int32] = []
  for c in 0..<cols {
    let mut piv = -1
    for r in rank..<rows {
      if a[r][c] % 2 != 0 {
        piv = r
        break
      }
    }
    if piv >= 0 {
      let tmp = a[piv]
      a[piv] = a[rank]
      a[rank] = tmp
      for r in 0..<rows {
        if r != rank && a[r][c] % 2 != 0 {
          for k in 0..<cols {
            a[r][k] = (a[r][k] + a[rank][k]) % 2
          }
        }
      }
      pivots.push(c)
      rank = rank + 1
    }
  }
  let out : Array[Array[Int32]] = []
  for i in 0..<rank {
    out.push(a[i].copy())
  }
  (out, pivots)
}

///|
/// 核空間的一組基底（每條向量長度 = 行數）。
pub fn b14_f2_kernel(m : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let rows = m.length()
  let cols = if rows == 0 { 0 } else { m[0].length() }
  let (r, pivots) = b14_f2_rref(m)
  let nr = r.length()
  let free : Array[Int32] = []
  for c in 0..<cols {
    let mut is_piv = false
    for p in pivots {
      if p == c {
        is_piv = true
      }
    }
    if !is_piv {
      free.push(c)
    }
  }
  let basis : Array[Array[Int32]] = []
  for f in free {
    let v : Array[Int32] = []
    for _ in 0..<cols {
      v.push(0)
    }
    v[f] = 1
    for i in 0..<nr {
      v[pivots[i]] = r[i][f]
    }
    basis.push(v)
  }
  basis
}

///|
/// 指定行數的核基底（處理「零列矩陣」的情形：0 列的矩陣其行數無法由形狀推得）。
pub fn b14_f2_kernel_n(
  m : Array[Array[Int32]],
  ncols : Int32,
) -> Array[Array[Int32]] {
  let rows = m.length()
  if rows == 0 {
    let out : Array[Array[Int32]] = []
    for j in 0..<ncols {
      let v : Array[Int32] = []
      for k in 0..<ncols {
        v.push(if k == j { 1 } else { 0 })
      }
      out.push(v)
    }
    return out
  }
  let have = m[0].length()
  let mm = b14_f2_zero(rows, ncols)
  for i in 0..<rows {
    for j in 0..<have {
      mm[i][j] = m[i][j]
    }
  }
  b14_f2_kernel(mm)
}

///|
/// 行空間基底（每條向量長度 = 列數），由逐列獨立性檢查得到。
pub fn b14_f2_col_basis(m : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let rows = m.length()
  let cols = if rows == 0 { 0 } else { m[0].length() }
  let basis : Array[Array[Int32]] = []
  for j in 0..<cols {
    let v : Array[Int32] = []
    for i in 0..<rows {
      v.push(m[i][j] % 2)
    }
    let trial : Array[Array[Int32]] = []
    for b in basis {
      trial.push(b)
    }
    trial.push(v)
    if b14_f2_rank(trial) > basis.length() {
      basis.push(v)
    }
  }
  basis
}

///|
/// 行空間的一個「標準補」：回傳若干標準基底向量 e_i 的索引，
/// 使它們與 m 的行空間共同張成整個 F₂^{rows}。
pub fn b14_f2_complement(m : Array[Array[Int32]]) -> Array[Int32] {
  let rows = m.length()
  let basis = b14_f2_col_basis(m)
  let out : Array[Int32] = []
  let mut rk = basis.length()
  for i in 0..<rows {
    let e : Array[Int32] = []
    for j in 0..<rows {
      e.push(if i == j { 1 } else { 0 })
    }
    let trial : Array[Array[Int32]] = []
    for b in basis {
      trial.push(b)
    }
    for b in out {
      let v : Array[Int32] = []
      for j in 0..<rows {
        v.push(if b == j { 1 } else { 0 })
      }
      trial.push(v)
    }
    trial.push(e)
    if b14_f2_rank(trial) > rk {
      out.push(i)
      rk = rk + 1
    }
  }
  out
}

///|
/// 解 K·X = B（K: rows×k，B: rows×m，求 X: k×m）。回傳 (可解, X)。
pub fn b14_f2_solve(
  k : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> (Bool, Array[Array[Int32]]) {
  let rows = k.length()
  let kc = if rows == 0 { 0 } else { k[0].length() }
  let m = if rows == 0 { 0 } else { b[0].length() }
  // 增廣矩陣 [K | B]，對 K 部分做 RREF，同時變換 B
  let a : Array[Array[Int32]] = []
  for r in 0..<rows {
    let row : Array[Int32] = []
    for j in 0..<kc {
      row.push(k[r][j] % 2)
    }
    for j in 0..<m {
      row.push(b[r][j] % 2)
    }
    a.push(row)
  }
  let mut rank = 0
  let pivots : Array[Int32] = []
  for c in 0..<kc {
    let mut piv = -1
    for r in rank..<rows {
      if a[r][c] % 2 != 0 {
        piv = r
        break
      }
    }
    if piv >= 0 {
      let tmp = a[piv]
      a[piv] = a[rank]
      a[rank] = tmp
      for r in 0..<rows {
        if r != rank && a[r][c] % 2 != 0 {
          for j in 0..<(kc + m) {
            a[r][j] = (a[r][j] + a[rank][j]) % 2
          }
        }
      }
      pivots.push(c)
      rank = rank + 1
    }
  }
  // 一致性：K 部分全零但 B 部分非零的列 ⇒ 無解
  let mut ok = true
  for r in 0..<rows {
    let mut z = true
    for j in 0..<kc {
      if a[r][j] % 2 != 0 {
        z = false
      }
    }
    if z {
      for j in 0..<m {
        if a[r][kc + j] % 2 != 0 {
          ok = false
        }
      }
    }
  }
  let x = b14_f2_zero(kc, m)
  if ok {
    for i in 0..<rank {
      for j in 0..<m {
        x[pivots[i]][j] = a[i][kc + j]
      }
    }
  }
  (ok, x)
}

///|
/// 單位矩陣。
pub fn b14_f2_id(n : Int32) -> Array[Array[Int32]] {
  let a : Array[Array[Int32]] = []
  for i in 0..<n {
    let row : Array[Int32] = []
    for j in 0..<n {
      row.push(if i == j { 1 } else { 0 })
    }
    a.push(row)
  }
  a
}

///|
/// 零矩陣。
pub fn b14_f2_zero(rows : Int32, cols : Int32) -> Array[Array[Int32]] {
  let a : Array[Array[Int32]] = []
  for _ in 0..<rows {
    let row : Array[Int32] = []
    for _ in 0..<cols {
      row.push(0)
    }
    a.push(row)
  }
  a
}

///|
/// F₂ 矩陣乘法。
pub fn b14_f2_mul(
  a : Array[Array[Int32]],
  b : Array[Array[Int32]],
) -> Array[Array[Int32]] {
  let rows = a.length()
  // inner 以 a 的每列長度為準（0 列 / 空列矩陣在截斷與 Čech 複形中會出現）
  let inner = if rows == 0 { 0 } else { a[0].length() }
  let cols = if b.length() == 0 { 0 } else { b[0].length() }
  let out : Array[Array[Int32]] = []
  for i in 0..<rows {
    let row : Array[Int32] = []
    for j in 0..<cols {
      let mut acc = 0
      for k in 0..<inner {
        if k < b.length() && k < a[i].length() {
          acc = acc + a[i][k] * b[k][j]
        }
      }
      row.push(acc % 2)
    }
    out.push(row)
  }
  out
}

///|
/// 轉置（凡迪耶／格羅滕迪克對偶用）。
pub fn b14_f2_transpose(m : Array[Array[Int32]]) -> Array[Array[Int32]] {
  let rows = m.length()
  let cols = if rows == 0 { 0 } else { m[0].length() }
  let out : Array[Array[Int32]] = []
  for j in 0..<cols {
    let row : Array[Int32] = []
    for i in 0..<rows {
      row.push(m[i][j])
    }
    out.push(row)
  }
  out
}

///|
/// 有限上鏈複形（F₂ 係數）：`diffs[q] : C^q → C^{q+1}`，`0 ≤ q < n−1`。
pub(all) struct B14Cx {
  n : Int32
  dims : Array[Int32]
  diffs : Array[Array[Array[Int32]]]
}

///|
/// 建構複形。
pub fn b14_cx(dims : Array[Int32], diffs : Array[Array[Array[Int32]]]) -> B14Cx {
  { n: dims.length(), dims, diffs, }
}

///|
/// 零複形。
pub fn b14_cx_zero(n : Int32) -> B14Cx {
  let dims : Array[Int32] = []
  let diffs : Array[Array[Array[Int32]]] = []
  for _ in 0..<n {
    dims.push(0)
  }
  for _ in 0..<(n - 1) {
    diffs.push(b14_f2_zero(0, 0))
  }
  b14_cx(dims, diffs)
}

///|
/// d² = 0 檢定，回傳 (是否成立, 非零項個數)。
pub fn b14_cx_ok(c : B14Cx) -> (Bool, Int32) {
  let mut bad = 0
  // d^q 與 d^{q+1} 可相乘的 q 只有 0 .. n-3
  for q in 0..<(c.n - 2) {
    let dd = b14_f2_mul(c.diffs[q + 1], c.diffs[q])
    for row in dd {
      for x in row {
        if x % 2 != 0 {
          bad = bad + 1
        }
      }
    }
  }
  (bad == 0, bad)
}

///|
/// 同調維數 h^q = dim ker d^q − rank d^{q−1}。
pub fn b14_cx_hom(c : B14Cx) -> Array[Int32] {
  let h : Array[Int32] = []
  for q in 0..<c.n {
    let k = if q == c.n - 1 {
      c.dims[q]
    } else {
      c.dims[q] - b14_f2_rank(c.diffs[q])
    }
    let r = if q > 0 { b14_f2_rank(c.diffs[q - 1]) } else { 0 }
    h.push(k - r)
  }
  h
}

///|
/// 歐拉特徵 Σ(−1)^q dim C^q。
pub fn b14_cx_euler(c : B14Cx) -> Int32 {
  let mut s = 0
  for q in 0..<c.n {
    let sign = if q % 2 == 0 { 1 } else { -1 }
    s = s + sign * c.dims[q]
  }
  s
}

///|
/// 第 q 度中第 p 塊（Hom(A^p, B^{p+q})）在向量化座標中的起點。
fn b14_hom_block_base(a : B14Cx, b : B14Cx, q : Int32, p : Int32) -> Int32 {
  let mut base = 0
  for p2 in 0..<p {
    let r2 = p2 + q
    if r2 >= 0 && r2 < b.n {
      base = base + a.dims[p2] * b.dims[r2]
    }
  }
  base
}

///|
/// Hom 複形：Hom^q = ⊕_p Hom(A^p, B^{p+q})，df = d_B f + f d_A（特徵 2 無符號）。
pub fn b14_hom_cx(a : B14Cx, b : B14Cx) -> B14Cx {
  let n = a.n + b.n
  let dims : Array[Int32] = []
  for q in 0..<n {
    let mut d = 0
    for p in 0..<a.n {
      let r = p + q
      if r >= 0 && r < b.n {
        d = d + a.dims[p] * b.dims[r]
      }
    }
    dims.push(d)
  }
  let diffs : Array[Array[Array[Int32]]] = []
  for q in 0..<(n - 1) {
    let mat = b14_f2_zero(dims[q + 1], dims[q])
    for p in 0..<a.n {
      let r = p + q
      if r < 0 || r >= b.n {
        continue
      }
      let src0 = b14_hom_block_base(a, b, q, p)
      // (d_B f)：目標塊 (p, r+1)，落於第 q+1 度
      if r + 1 < b.n && p + (q + 1) < b.n {
        let dst0 = b14_hom_block_base(a, b, q + 1, p)
        for i in 0..<a.dims[p] {
          for j in 0..<b.dims[r] {
            let src = src0 + i * b.dims[r] + j
            for j2 in 0..<b.dims[r + 1] {
              if b.diffs[r][j2][j] % 2 != 0 {
                let dst = dst0 + i * b.dims[r + 1] + j2
                if dst < dims[q + 1] && src < dims[q] {
                  mat[dst][src] = (mat[dst][src] + 1) % 2
                }
              }
            }
          }
        }
      }
      // (f d_A)：目標塊 (p−1, r)，落於第 q+1 度
      if p >= 1 && a.n >= 2 {
        let dst0 = b14_hom_block_base(a, b, q + 1, p - 1)
        for i in 0..<a.dims[p] {
          for j in 0..<b.dims[r] {
            let src = src0 + i * b.dims[r] + j
            for i2 in 0..<a.dims[p - 1] {
              if a.diffs[p - 1][i][i2] % 2 != 0 {
                let dst = dst0 + i2 * b.dims[r] + j
                if dst < dims[q + 1] && src < dims[q] {
                  mat[dst][src] = (mat[dst][src] + 1) % 2
                }
              }
            }
          }
        }
      }
    }
    diffs.push(mat)
  }
  b14_cx(dims, diffs)
}

///|
/// dim Hom_D(A, B) = h^0(Hom^*(A, B))。
pub fn b14_hom_dim(a : B14Cx, b : B14Cx) -> Int32 {
  b14_cx_hom(b14_hom_cx(a, b))[0]
}

///|
/// 標準 t-結構的左截斷 τ_{≤k}（構造真實複形，非僅記維數）：
/// C'^q = C^q (q<k)、C'^k = ker d^k、C'^q = 0 (q>k)。
pub fn b14_cx_trunc_le(c : B14Cx, k : Int32) -> B14Cx {
  if k >= c.n - 1 {
    return c
  }
  if k < 0 {
    let dims : Array[Int32] = []
    for _ in 0..<c.n {
      dims.push(0)
    }
    let diffs : Array[Array[Array[Int32]]] = []
    for _ in 0..<(c.n - 1) {
      diffs.push(b14_f2_zero(0, 0))
    }
    return b14_cx(dims, diffs)
  }
  let ker = b14_f2_kernel_n(c.diffs[k], c.dims[k]) // 每條長度 = c.dims[k]
  let r = c.dims[k] - b14_f2_rank(c.diffs[k])
  let dims : Array[Int32] = []
  for q in 0..<c.n {
    if q < k {
      dims.push(c.dims[q])
    } else if q == k {
      dims.push(r)
    } else {
      dims.push(0)
    }
  }
  // K: c.dims[k] × r
  let kmat = b14_f2_transpose(ker)
  let diffs : Array[Array[Array[Int32]]] = []
  for q in 0..<(c.n - 1) {
    if q < k - 1 {
      diffs.push(c.diffs[q])
    } else if q == k - 1 {
      let (ok, x) = b14_f2_solve(kmat, c.diffs[k - 1])
      if ok {
        diffs.push(x)
      } else {
        diffs.push(b14_f2_zero(dims[k], dims[q]))
      }
    } else {
      diffs.push(b14_f2_zero(dims[q + 1], dims[q]))
    }
  }
  b14_cx(dims, diffs)
}

///|
/// 標準 t-結構的右截斷 τ_{≥k}：C'^k = coker(d^{k−1})、C'^q = C^q (q>k)、C'^q = 0 (q<k)。
pub fn b14_cx_trunc_ge(c : B14Cx, k : Int32) -> B14Cx {
  if k <= 0 {
    return c
  }
  if k >= c.n {
    let dims : Array[Int32] = []
    for _ in 0..<c.n {
      dims.push(0)
    }
    let diffs : Array[Array[Array[Int32]]] = []
    for _ in 0..<(c.n - 1) {
      diffs.push(b14_f2_zero(0, 0))
    }
    return b14_cx(dims, diffs)
  }
  let mut s = c.dims[k]
  let mut rep : Array[Int32] = []
  if k > 0 {
    let comp = b14_f2_complement(c.diffs[k - 1])
    s = comp.length()
    rep = comp
  } else {
    rep = []
    for i in 0..<c.dims[k] {
      rep.push(i)
    }
  }
  let dims : Array[Int32] = []
  for q in 0..<c.n {
    if q < k {
      dims.push(0)
    } else if q == k {
      dims.push(s)
    } else {
      dims.push(c.dims[q])
    }
  }
  // R: c.dims[k] × s（代表元）
  let rmat = b14_f2_zero(c.dims[k], s)
  for j in 0..<s {
    rmat[rep[j]][j] = 1
  }
  let diffs : Array[Array[Array[Int32]]] = []
  for q in 0..<(c.n - 1) {
    if q < k - 1 {
      diffs.push(b14_f2_zero(dims[q + 1], dims[q]))
    } else if q == k - 1 {
      diffs.push(b14_f2_zero(dims[q + 1], dims[q]))
    } else if q == k {
      diffs.push(b14_f2_mul(c.diffs[k], rmat))
    } else {
      diffs.push(c.diffs[q])
    }
  }
  b14_cx(dims, diffs)
}
