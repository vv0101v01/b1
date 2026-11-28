///|
/// toposw.mbt — 批次八·模組 5：無窮組合拓撲斯中的範疇化代數不變量
///
/// 範疇化不變量以「群胚基數」與「單純同調」兩種方式計算：
///   1. 群胚基數 χ(G) = Σ_{物件} 1/|Aut|（精確有理數）：這是「數」的範疇化提升，
///      滿足 χ(G × H) = χ(G)·χ(H)、χ(G ⊔ H) = χ(G) + χ(H)。
///   2. 有限單純複形的 Betti 數（以質數模線性代數精確算秩），
///      並驗證歐拉—龐加萊恆等式 χ = Σ (-1)^i b_i。
///   3. 範疇神經的鏈數 N_n（可複合 n 元組之數），以及對群胚 χ(BG) = 1/|G|。
///   4. 有限組合性質的「無窮極限提升」：對單調塔取其穩定值。

// ───────────────────────── 有理數運算 ─────────────────────────

///|
/// 最大公因數。
fn b8w_gcd(a : Int64, b : Int64) -> Int64 {
  let mut x = if a < 0L { -a } else { a }
  let mut y = if b < 0L { -b } else { b }
  while y != 0L {
    let t = x % y
    x = y
    y = t
  }
  if x == 0L {
    1L
  } else {
    x
  }
}

///|
/// 有理數（分子, 分母），分母恆正且已約分。
pub fn b8w_rat(n : Int64, d : Int64) -> (Int64, Int64) {
  let g = b8w_gcd(n, d)
  let mut nn = n / g
  let mut dd = d / g
  if dd < 0L {
    nn = -nn
    dd = -dd
  }
  (nn, dd)
}

///|
/// 有理數加法。
pub fn b8w_rat_add(a : (Int64, Int64), b : (Int64, Int64)) -> (Int64, Int64) {
  b8w_rat(a.0 * b.1 + b.0 * a.1, a.1 * b.1)
}
// ───────────────────────── 範疇的群胚基數 ─────────────────────────

///|
/// 態射 m 是否可逆。
pub fn b8w_is_iso(c : B8Cat, m : Int32) -> Bool {
  let a = c.dom[m]
  let b = c.cod[m]
  for n in 0..<c.nmor {
    if c.dom[n] == b && c.cod[n] == a {
      if c.cmp[n * c.nmor + m] == c.idm[a] && c.cmp[m * c.nmor + n] == c.idm[b] {
        return true
      }
    }
  }
  false
}

///|
/// 物件的自同構群大小。
pub fn b8w_aut_size(c : B8Cat, a : Int32) -> Int32 {
  let mut k = 0
  for m in 0..<c.nmor {
    if c.dom[m] == a && c.cod[m] == a && b8w_is_iso(c, m) {
      k = k + 1
    }
  }
  k
}

///|
/// 兩物件在同構意義下是否等價（存在可逆態射 a → b）。
pub fn b8w_iso_obj(c : B8Cat, a : Int32, b : Int32) -> Bool {
  if a == b {
    return true
  }
  for m in 0..<c.nmor {
    if c.dom[m] == a && c.cod[m] == b && b8w_is_iso(c, m) {
      return true
    }
  }
  false
}

///|
/// 群胚基數（核心的範疇化基數）：χ = Σ_{同構類} 1/|Aut|。
pub fn b8w_core_card(c : B8Cat) -> (Int64, Int64) {
  let mut acc = b8w_rat(0L, 1L)
  for a in 0..<c.nob {
    // 只計同構類的代表（最小編號）
    let mut rep = true
    for b in 0..<a {
      if b8w_iso_obj(c, b, a) {
        rep = false
      }
    }
    if rep {
      let k = b8w_aut_size(c, a)
      if k > 0 {
        acc = b8w_rat_add(acc, b8w_rat(1L, k.to_int64()))
      }
    }
  }
  acc
}

///|
/// 範疇的乘積（物件與態射皆成對）。
pub fn b8w_cat_prod(a : B8Cat, b : B8Cat) -> B8Cat {
  let nob = a.nob * b.nob
  let nmor = a.nmor * b.nmor
  let dom : Array[Int32] = []
  let cod : Array[Int32] = []
  let idm : Array[Int32] = []
  let cmp : Array[Int32] = []
  for i in 0..<a.nob {
    for j in 0..<b.nob {
      idm.push(i * b.nob + j)
    }
  }
  for m in 0..<a.nmor {
    for n in 0..<b.nmor {
      dom.push(a.dom[m] * b.nob + b.dom[n])
      cod.push(a.cod[m] * b.nob + b.cod[n])
    }
  }
  for m in 0..<a.nmor {
    for n in 0..<b.nmor {
      for m2 in 0..<a.nmor {
        for n2 in 0..<b.nmor {
          // (g,h) ∘ (m,n) = (g∘m, h∘n)
          let g = m2
          let f = m
          let h = n2
          let k = n
          if a.cod[f] == a.dom[g] && b.cod[k] == b.dom[h] {
            let comp = a.cmp[g * a.nmor + f] * b.nmor + b.cmp[h * b.nmor + k]
            cmp.push(comp)
          } else {
            cmp.push(-1)
          }
        }
      }
    }
  }
  b8_cat_make(nob, nmor, dom, cod, idm, cmp)
}

///|
/// 範疇神經的鏈數：N_n = 可複合 n 元組 (f_1,…,f_n) 之數（n = 0 時為物件數）。
pub fn b8w_nerve_count(c : B8Cat, n : Int32) -> @bigint.BigInt {
  if n == 0 {
    return @bigint.BigInt::from_int(c.nob.to_int())
  }
  let mut cur : Array[@bigint.BigInt] = []
  for _ in 0..<c.nmor {
    cur.push(@bigint.BigInt::from_int(1))
  }
  for _ in 1..<n {
    let nxt : Array[@bigint.BigInt] = []
    for g in 0..<c.nmor {
      let mut acc = @bigint.BigInt::from_int(0)
      for f in 0..<c.nmor {
        if c.cod[f] == c.dom[g] {
          acc = acc + cur[f]
        }
      }
      nxt.push(acc)
    }
    cur = nxt
  }
  let mut tot = @bigint.BigInt::from_int(0)
  for v in cur {
    tot = tot + v
  }
  tot
}

// ───────────────────────── 單純複形的 Betti 數 ─────────────────────────

///|
/// 在清單中尋找（或加入）以排序陣列為鍵的項目。
fn b8w_find_or_add(keys : Array[Array[Int32]], k : Array[Int32]) -> Int32 {
  for i in 0..<keys.length() {
    if b_sh_arr_eq(keys[i], k) {
      return i
    }
  }
  keys.push(k)
  keys.length() - 1
}

///|
/// 由極大單形（排序後的頂點清單）生成整個複形的各維單形（維度 0…maxdim）。
pub fn b8w_complex(
  maxsimplices : Array[Array[Int32]],
) -> Array[Array[Array[Int32]]] {
  let mut maxdim = 0
  for s in maxsimplices {
    if s.length() - 1 > maxdim {
      maxdim = s.length() - 1
    }
  }
  let levels : Array[Array[Array[Int32]]] = []
  for _ in 0..<(maxdim + 1) {
    let empty : Array[Array[Int32]] = []
    levels.push(empty)
  }
  for s in maxsimplices {
    // 所有子集
    let n = s.length()
    for mask in 0..<b8u_pow2_int(n) {
      let sub : Array[Int32] = []
      for b in 0..<n {
        if ((mask >> b) & 1) == 1 {
          sub.push(s[b])
        }
      }
      if sub.length() > 0 {
        let _ = b8w_find_or_add(levels[sub.length() - 1], sub)
      }
    }
  }
  levels
}

///|
/// 模 p 的矩陣秩（列形式）。
fn b8w_rank_mod(rows : Array[Array[Int32]], p : Int64) -> Int32 {
  let m : Array[Array[Int64]] = []
  for r in rows {
    let rr : Array[Int64] = []
    for v in r {
      let mut x = v.to_int64() % p
      if x < 0L {
        x = x + p
      }
      rr.push(x)
    }
    m.push(rr)
  }
  let nrow = m.length()
  if nrow == 0 {
    return 0
  }
  let ncol = m[0].length()
  let mut rank = 0
  let mut col = 0
  while col < ncol && rank < nrow {
    // 找樞軸
    let mut piv = -1
    for r in rank..<nrow {
      if m[r][col] != 0L {
        piv = r
        break
      }
    }
    if piv < 0 {
      col = col + 1
      continue
    }
    // 交換
    let tmp = m[rank]
    m[rank] = m[piv]
    m[piv] = tmp
    // 消去（以模反元素）
    let inv = b8w_modinv(m[rank][col], p)
    for r in 0..<nrow {
      if r != rank && m[r][col] != 0L {
        let f = m[r][col] * inv % p
        for c in 0..<ncol {
          m[r][c] = (m[r][c] - f * m[rank][c]) % p
          if m[r][c] < 0L {
            m[r][c] = m[r][c] + p
          }
        }
      }
    }
    rank = rank + 1
    col = col + 1
  }
  rank
}

///|
/// 模 p 的乘法反元素（費馬小定理）。
fn b8w_modinv(a : Int64, p : Int64) -> Int64 {
  let mut r = 1L
  let mut b = a % p
  let mut e = p - 2L
  while e > 0L {
    if e % 2L == 1L {
      r = r * b % p
    }
    b = b * b % p
    e = e / 2L
  }
  r
}

///|
/// 有限單純複形的 Betti 數（以質數 1000000007 與 998244353 之秩取較大者，實務上等於有理秩）。
pub fn b8w_betti(maxsimplices : Array[Array[Int32]]) -> Array[Int32] {
  let levels = b8w_complex(maxsimplices)
  let ndim = levels.length()
  let ranks : Array[Int32] = []
  for d in 1..<ndim {
    // ∂_d：列 = (d-1)-單形，行 = d-單形
    let below = levels[d - 1]
    let here = levels[d]
    let rows : Array[Array[Int32]] = []
    for _ in 0..<below.length() {
      let r : Array[Int32] = []
      for _ in 0..<here.length() {
        r.push(0)
      }
      rows.push(r)
    }
    for j in 0..<here.length() {
      let t = here[j]
      for i in 0..<t.length() {
        let face : Array[Int32] = []
        for k in 0..<t.length() {
          if i != k {
            face.push(t[k])
          }
        }
        let fi = b8w_find_or_add(below, face)
        if fi < below.length() {
          rows[fi][j] = if i % 2 == 0 { 1 } else { -1 }
        }
      }
    }
    let r1 = b8w_rank_mod(rows, 1000000007L)
    let r2 = b8w_rank_mod(rows, 998244353L)
    ranks.push(if r1 > r2 { r1 } else { r2 })
  }
  let betti : Array[Int32] = []
  for d in 0..<ndim {
    let nd = levels[d].length()
    let rk_d = if d == 0 { 0 } else { ranks[d - 1] }
    let rk_next = if d + 1 < ndim { ranks[d] } else { 0 }
    betti.push(nd - rk_d - rk_next)
  }
  betti
}

///|
/// 單純複形的歐拉特徵（單形計數的交替和）。
pub fn b8w_euler_complex(maxsimplices : Array[Array[Int32]]) -> Int32 {
  let levels = b8w_complex(maxsimplices)
  let mut e = 0
  for d in 0..<levels.length() {
    let n = levels[d].length()
    e = e + (if d % 2 == 0 { n } else { -n })
  }
  e
}

///|
/// 歐拉—龐加萊：χ = Σ (-1)^i b_i。
pub fn b8w_euler_betti(maxsimplices : Array[Array[Int32]]) -> Int32 {
  let b = b8w_betti(maxsimplices)
  let mut e = 0
  for d in 0..<b.length() {
    e = e + (if d % 2 == 0 { b[d] } else { -b[d] })
  }
  e
}

///|
/// 標準 n 維實心單形（頂點 0…n）的單純複形。
pub fn b8w_simplex(n : Int32) -> Array[Array[Int32]] {
  let v : Array[Int32] = []
  for i in 0..<=n {
    v.push(i)
  }
  [v]
}

///|
/// n 維球面（n+1 個頂點上的邊界）作為單純複形：所有 (n+1) 元子集（即全部 n-單形）。
pub fn b8w_sphere(n : Int32) -> Array[Array[Int32]] {
  let out : Array[Array[Int32]] = []
  let k = n + 2
  for skip in 0..<k {
    let v : Array[Int32] = []
    for i in 0..<k {
      if i != skip {
        v.push(i)
      }
    }
    out.push(v)
  }
  out
}

// ───────────────────────── 極限提升 ─────────────────────────
