///|
/// catcore.mbt — 批次八·模組 1：點函子（point functor）與評估函子（evaluation functor）
///
/// 有限範疇 C 以「物件數 / 態射數 / dom / cod / id / 合成表」顯式表示；
/// 預層（presheaf）F : C^op → Set 以「每個物件上的有限集合 + 每個態射上的限制映射」表示。
/// 自然變換以逐物件函數族表示，並以**弧相容剪枝的回溯搜索**精確計算 Nat 集的**元素個數**
/// （而非暴力枚舉全部函數族，故可處理 8 個以上插槽的情形）。
///
/// 由此可把下列定理變成可數的等式：
///   點函子 ev_c = Nat(よ(c), −)（Yoneda）  ⇒ |Nat(よc, F)| = |F(c)|
///   ev_c 保極限 / 保餘極限（左右伴隨）      ⇒ 乘積／餘積的 Nat 數相等
///   ev_c 的左伴隨 A ⊗ よc                    ⇒ |Nat(A⊗よc, F)| = |F(c)|^A
///   ev_c 的右伴隨（cofree）GA(d) = A^{Hom(d,c)} ⇒ |Nat(F, GA)| = A^{|F(c)|}

// ───────────────────────── 有限範疇 ─────────────────────────

///|
/// 有限範疇。cmp[g*nmor+f] = g ∘ f（僅在 cod f = dom g 時有意義）。
pub(all) struct B8Cat {
  nob : Int32
  nmor : Int32
  dom : Array[Int32]
  cod : Array[Int32]
  idm : Array[Int32]
  cmp : Array[Int32]
}

///|
/// 以平坦陣列建構範疇：dom/cod 長度 = nmor，idm 長度 = nob，cmp 長度 = nmor²。
pub fn b8_cat_make(
  nob : Int32,
  nmor : Int32,
  dom : Array[Int32],
  cod : Array[Int32],
  idm : Array[Int32],
  cmp : Array[Int32],
) -> B8Cat {
  { nob, nmor, dom, cod, idm, cmp, }
}

///|
/// 範疇公理：id 的左右單位律、合成型的 dom/cod、結合律。
pub fn b8_cat_ok(c : B8Cat) -> Bool {
  for a in 0..<c.nob {
    let e = c.idm[a]
    if c.dom[e] != a || c.cod[e] != a {
      return false
    }
    for f in 0..<c.nmor {
      if c.dom[f] == a && c.cmp[f * c.nmor + e] != f {
        return false
      }
      if c.cod[f] == a && c.cmp[e * c.nmor + f] != f {
        return false
      }
    }
  }
  for g in 0..<c.nmor {
    for f in 0..<c.nmor {
      if c.cod[f] == c.dom[g] {
        let h = c.cmp[g * c.nmor + f]
        if h < 0 || c.dom[h] != c.dom[f] || c.cod[h] != c.cod[g] {
          return false
        }
      }
    }
  }
  for h in 0..<c.nmor {
    for g in 0..<c.nmor {
      for f in 0..<c.nmor {
        if c.cod[f] == c.dom[g] && c.cod[g] == c.dom[h] {
          let left = c.cmp[h * c.nmor + c.cmp[g * c.nmor + f]]
          let right = c.cmp[c.cmp[h * c.nmor + g] * c.nmor + f]
          if left != right {
            return false
          }
        }
      }
    }
  }
  true
}

///|
/// 以「恆等律 + 明確列出的非平凡合成」建構範疇的合成表。
/// extra 的元素為 (g, f, g∘f)，其餘可合成對由單位律決定；未填者可合成對會使 b8_cat_ok 失敗。
pub fn b8_cat_build(
  nob : Int32,
  nmor : Int32,
  dom : Array[Int32],
  cod : Array[Int32],
  idm : Array[Int32],
  extra : Array[(Int32, Int32, Int32)],
) -> B8Cat {
  let cmp : Array[Int32] = []
  for _ in 0..<(nmor * nmor) {
    cmp.push(-1)
  }
  for f in 0..<nmor {
    cmp[f * nmor + idm[dom[f]]] = f
    cmp[idm[cod[f]] * nmor + f] = f
  }
  for (g, f, h) in extra {
    cmp[g * nmor + f] = h
  }
  b8_cat_make(nob, nmor, dom, cod, idm, cmp)
}

///|
/// 走路箭頭範疇 0 → 1。態射：0=id₀、1=f、2=id₁。
pub fn b8_cat_arrow() -> B8Cat {
  b8_cat_build(2, 3, [0, 0, 1], [0, 1, 1], [0, 2], [(1, 0, 1), (2, 1, 1)])
}

///|
/// 平行對 0 ⇉ 1。態射：0=id₀、1=f、2=g、3=id₁。
pub fn b8_cat_par() -> B8Cat {
  b8_cat_build(2, 4, [0, 0, 0, 1], [0, 1, 1, 1], [0, 3], [
    (1, 0, 1),
    (2, 0, 2),
    (3, 1, 1),
    (3, 2, 2),
  ])
}

///|
/// 走路同構 0 ≅ 1（態射：0=id₀、1=f:0→1、2=f⁻¹:1→0、3=id₁）。
pub fn b8_cat_iso() -> B8Cat {
  b8_cat_build(2, 4, [0, 0, 1, 1], [0, 1, 0, 1], [0, 3], [
    (1, 0, 1),
    (1, 2, 3),
    (2, 3, 2),
    (2, 1, 0),
  ])
}

///|
/// 單物件範疇（么半、群）：n 個態射，全部 dom=cod=0。
pub fn b8_cat_monoid(n : Int32, mult : Array[Int32]) -> B8Cat {
  let dom : Array[Int32] = []
  let cod : Array[Int32] = []
  for _ in 0..<n {
    dom.push(0)
    cod.push(0)
  }
  b8_cat_make(1, n, dom, cod, [0], mult)
}

///|
/// Z/2 視為單物件群（態射 0=e、1=g；乘法 = xor）。
pub fn b8_cat_z2() -> B8Cat {
  b8_cat_monoid(2, [0, 1, 1, 0])
}

///|
/// 走路餘等化子（span）0 ← 1 → 2：態射 0=id₀、1=id₁、2=id₂、3=a:1→0、4=b:1→2。
/// 所有非恆等態射的定義域皆為 1，故非恆等態射之間無可合成對。
pub fn b8_cat_span() -> B8Cat {
  b8_cat_build(3, 5, [0, 1, 2, 1, 1], [0, 1, 2, 0, 2], [0, 1, 2], [])
}

///|
/// 由兩個裝訂（0≤a≤1, 0≤b≤1）構成的交換方格：4 物件、9 態射。
/// 物件 (a,b) 編號 a*2+b：00=0, 01=1, 10=2, 11=3。
/// 態射：id 4 個 (0..3) + h0:0→1 (4)、h1:2→3 (5)、v0:0→2 (6)、v1:1→3 (7)、d:0→3 (8)。
pub fn b8_cat_square() -> B8Cat {
  b8_cat_build(
    4,
    9,
    [0, 1, 2, 3, 0, 2, 0, 1, 0],
    [0, 1, 2, 3, 1, 3, 2, 3, 3],
    [0, 1, 2, 3],
    [(7, 4, 8), (5, 6, 8)],
  )
}

///|
/// 離散範疇（n 個物件、只有恆等態射）。
pub fn b8_cat_disc(n : Int32) -> B8Cat {
  let dom : Array[Int32] = []
  let cod : Array[Int32] = []
  let idm : Array[Int32] = []
  let cmp : Array[Int32] = []
  for a in 0..<n {
    dom.push(a)
    cod.push(a)
    idm.push(a)
  }
  for g in 0..<n {
    for f in 0..<n {
      cmp.push(if g == f { g } else { -1 })
    }
  }
  b8_cat_make(n, n, dom, cod, idm, cmp)
}

///|
/// Hom 集：物件 d → c 的所有態射（遞增順序）。
pub fn b8_hom(c : B8Cat, d : Int32, cc : Int32) -> Array[Int32] {
  let out : Array[Int32] = []
  for m in 0..<c.nmor {
    if c.dom[m] == d && c.cod[m] == cc {
      out.push(m)
    }
  }
  out
}

// ───────────────────────── 預層與自然變換 ─────────────────────────

///|
/// 有限預層：sz[c] = |F(c)|；res[m*mx + j] = F(m)(j)（m: a→b 時為 F(b)→F(a)）。
pub(all) struct B8PS {
  cat : B8Cat
  sz : Array[Int32]
  mx : Int32
  res : Array[Int32]
}

///|
/// 由每物件大小與限制映射建構預層（mx 由 sz 的最大值決定）。
pub fn b8_ps_make(cat : B8Cat, sz : Array[Int32], res : Array[Int32]) -> B8PS {
  let mut mx = 1
  for s in sz {
    if s > mx {
      mx = s
    }
  }
  { cat, sz, mx, res, }
}

///|
/// 預層的「行距」（res 的 stride）：max(1, max sz)，與 b8_ps_make 的 mx 一致。
fn b8_ps_st(sz : Array[Int32]) -> Int32 {
  let mut st = 1
  for s in sz {
    if s > st {
      st = s
    }
  }
  st
}

///|
/// 常數預層（每物件 n 個元素、限制為恆等）。
pub fn b8_ps_const(cat : B8Cat, n : Int32) -> B8PS {
  let sz : Array[Int32] = []
  for _ in 0..<cat.nob {
    sz.push(n)
  }
  let mx = if n < 1 { 1 } else { n }
  let res : Array[Int32] = []
  for _ in 0..<(cat.nmor * mx) {
    res.push(0)
  }
  for m in 0..<cat.nmor {
    for j in 0..<mx {
      res[m * mx + j] = if j < n { j } else { 0 }
    }
  }
  b8_ps_make(cat, sz, res)
}

///|
/// 可表預層 よ(cc)：よc(d) = Hom(d, c)，限制為前合成。
pub fn b8_ps_yoneda(c : B8Cat, cc : Int32) -> B8PS {
  let sz : Array[Int32] = []
  let mut mx = 1
  for d in 0..<c.nob {
    let n = b8_hom(c, d, cc).length()
    sz.push(n)
    if n > mx {
      mx = n
    }
  }
  let homs : Array[Array[Int32]] = []
  for d in 0..<c.nob {
    homs.push(b8_hom(c, d, cc))
  }
  let res : Array[Int32] = []
  for _ in 0..<(c.nmor * mx) {
    res.push(0)
  }
  for m in 0..<c.nmor {
    let hb = homs[c.cod[m]]
    let ha = homs[c.dom[m]]
    for j in 0..<mx {
      if j < hb.length() {
        let g = hb[j]
        let gm = c.cmp[g * c.nmor + m]
        let mut pos = 0
        for k in 0..<ha.length() {
          if ha[k] == gm {
            pos = k
          }
        }
        res[m * mx + j] = pos
      }
    }
  }
  b8_ps_make(c, sz, res)
}

///|
/// LCG 步進（回傳新種子）。
fn b8_lcg(s : Int64) -> Int64 {
  s * 6364136223846793005L + 1442695040888963407L
}

///|
/// 由 LCG 產生「隨機」預層——但**保證是真正的預層**：
/// 取若干個可表預層（及其兩兩乘積）之**餘積**，即 F = ⊔ₖ Gₖ，Gₖ ∈ {よ(cₖ), よ(cₖ)×よ(dₖ)}。
/// 餘積與乘積皆逐物件計算，故仍是預層，且限制映射自動滿足函子性。
pub fn b8_ps_rand(cat : B8Cat, seed : Int64) -> B8PS {
  let nob = cat.nob.to_int()
  let mut s = b8_lcg(seed)
  let nfac = ((s >> 33).to_int() % 3).abs() + 1
  let mut acc = b8_ps_const(cat, 0)
  for _ in 0..<nfac {
    s = b8_lcg(s)
    let c1 = ((s >> 33).to_int() % nob).abs()
    let mut g = b8_ps_yoneda(cat, c1)
    s = b8_lcg(s)
    if ((s >> 33).to_int() % 4).abs() == 0 {
      s = b8_lcg(s)
      let c2 = ((s >> 33).to_int() % nob).abs()
      g = b8_ps_prod(g, b8_ps_yoneda(cat, c2))
    }
    acc = b8_ps_coprod(acc, g)
  }
  acc
}

///|
/// 是否為良定義的預層：res[id] = id、res[m∘m'] = res[m']∘res[m]。
pub fn b8_ps_ok(f : B8PS) -> Bool {
  let c = f.cat
  let mx = f.mx
  // 恆等
  for a in 0..<c.nob {
    let e = c.idm[a]
    for j in 0..<f.sz[a] {
      if f.res[e * mx + j] != j {
        return false
      }
    }
  }
  // 函子性
  for m in 0..<c.nmor {
    for n in 0..<c.nmor {
      if c.cod[n] == c.dom[m] {
        let mn = c.cmp[m * c.nmor + n]
        for j in 0..<f.sz[c.cod[m]] {
          let lhs = f.res[mn * mx + j]
          let mid = f.res[m * mx + j]
          let rhs = f.res[n * mx + mid]
          if lhs != rhs {
            return false
          }
        }
      }
    }
  }
  true
}

///|
/// 逐物件乘積（編碼：以 g.sz[cod m] 為進位的配對碼）。
pub fn b8_ps_prod(f : B8PS, g : B8PS) -> B8PS {
  let cat = f.cat
  let sz : Array[Int32] = []
  for c in 0..<cat.nob {
    sz.push(f.sz[c] * g.sz[c])
  }
  let st = b8_ps_st(sz)
  let res : Array[Int32] = []
  for _ in 0..<(cat.nmor * st) {
    res.push(0)
  }
  for m in 0..<cat.nmor {
    let b = cat.cod[m]
    let gs = g.sz[b]
    for j in 0..<sz[b] {
      let fi = j / gs
      let gi = j % gs
      let nf = f.res[m * f.mx + fi]
      let ng = g.res[m * g.mx + gi]
      res[m * st + j] = nf * gs + ng
    }
  }
  b8_ps_make(cat, sz, res)
}

///|
/// 逐物件餘積（不交並；第二塊的偏移取 |F(dom m)|）。
pub fn b8_ps_coprod(f : B8PS, g : B8PS) -> B8PS {
  let cat = f.cat
  let sz : Array[Int32] = []
  for c in 0..<cat.nob {
    sz.push(f.sz[c] + g.sz[c])
  }
  let st = b8_ps_st(sz)
  let res : Array[Int32] = []
  for _ in 0..<(cat.nmor * st) {
    res.push(0)
  }
  for m in 0..<cat.nmor {
    let b = cat.cod[m]
    let a = cat.dom[m]
    for j in 0..<sz[b] {
      if j < f.sz[b] {
        res[m * st + j] = f.res[m * f.mx + j]
      } else {
        res[m * st + j] = f.sz[a] + g.res[m * g.mx + (j - f.sz[b])]
      }
    }
  }
  b8_ps_make(cat, sz, res)
}

///|
/// A 份 よ(c) 的餘積（ev_c 的左伴隨：A ↦ A ⊗ よc）。
pub fn b8_ps_free_yoneda(cat : B8Cat, cc : Int32, a : Int32) -> B8PS {
  let y = b8_ps_yoneda(cat, cc)
  let mut acc = b8_ps_const(cat, 0)
  for _ in 0..<a {
    acc = b8_ps_coprod(acc, y)
  }
  acc
}

///|
/// cofree 預層：G_A(d) = A^{Hom(c,d)}（ev_c 的右伴隨）。
/// 元素以 r 進位整數編碼 Hom(c,d) 上的函數值；限制映射 = 沿 m 後合成後重新編碼。
pub fn b8_ps_cofree(cat : B8Cat, cc : Int32, a : Int32) -> B8PS {
  let sz : Array[Int32] = []
  let mut mx = 1
  for d in 0..<cat.nob {
    let n = b8_pow_int(a, b8_hom(cat, cc, d).length())
    sz.push(n)
    if n > mx {
      mx = n
    }
  }
  let homs : Array[Array[Int32]] = []
  for d in 0..<cat.nob {
    homs.push(b8_hom(cat, cc, d))
  }
  let res : Array[Int32] = []
  for _ in 0..<(cat.nmor * mx) {
    res.push(0)
  }
  for m in 0..<cat.nmor {
    let ha = homs[cat.dom[m]]
    let hb = homs[cat.cod[m]]
    for j in 0..<mx {
      if j < sz[cat.cod[m]] {
        // j 編碼 φ : Hom(c, cod m) → A；結果 φ ∘ (−; m) 在 Hom(c, dom m) 上的值
        let mut acc = 0
        for k in 0..<ha.length() {
          let t = ha[k]
          let mt = cat.cmp[m * cat.nmor + t]
          let mut val = 0
          for p in 0..<hb.length() {
            if hb[p] == mt {
              val = b8_digit(j, a, p)
            }
          }
          acc = acc + val * b8_pow_int(a, k)
        }
        res[m * mx + j] = acc
      }
    }
  }
  b8_ps_make(cat, sz, res)
}

///|
/// 整數冪（a^k，k ≥ 0）。
pub fn b8_pow_int(a : Int32, k : Int32) -> Int32 {
  let mut r = 1
  for _ in 0..<k {
    r = r * a
  }
  r
}

///|
/// 取 r 進位數的第 k 位。
fn b8_digit(x : Int32, r : Int32, k : Int32) -> Int32 {
  if r <= 1 {
    return 0
  }
  let mut d = x
  for _ in 0..<k {
    d = d / r
  }
  d % r
}

// ───────────────────────── 自然變換的計數 ─────────────────────────

///|
/// 定義域表：dmask[slot*rad + v] 表示「插槽 slot 可取候選值 v」。
/// 以布林陣列（而非位元遮罩）表示，故候選值個數 rad 不設上限。
fn b8_ac3(
  dmask : Array[Bool],
  cA : Array[Int32],
  cB : Array[Int32],
  cF : Array[Int32],
  rad : Int32,
  nslot : Int32,
  _total : Int32,
) -> Bool {
  let mut changed = true
  while changed {
    changed = false
    // 若有插槽定義域變空則失敗
    for i in 0..<nslot {
      let mut any = false
      for v in 0..<rad {
        if dmask[i * rad + v] {
          any = true
        }
      }
      if !any {
        return false
      }
    }
    for idx in 0..<cA.length() {
      let ia = cA[idx]
      let ib = cB[idx]
      // (1) 若 ib 的候選 v 之像不在 ia 的定義域，刪除 v
      for v in 0..<rad {
        if dmask[ib * rad + v] {
          let u = cF[idx * rad + v]
          if !dmask[ia * rad + u] {
            dmask[ib * rad + v] = false
            changed = true
          }
        }
      }
      // (2) 若 ia 的候選 u 沒有原像在 ib 的定義域，刪除 u
      for u in 0..<rad {
        if dmask[ia * rad + u] {
          let mut has = false
          for v in 0..<rad {
            if dmask[ib * rad + v] && cF[idx * rad + v] == u {
              has = true
            }
          }
          if !has {
            dmask[ia * rad + u] = false
            changed = true
          }
        }
      }
    }
  }
  true
}

///|
/// 在給定定義域下以回溯搜索計數解（挑候選最少且 >1 的插槽分支）。
fn b8_count_sol(
  dmask : Array[Bool],
  cA : Array[Int32],
  cB : Array[Int32],
  cF : Array[Int32],
  rad : Int32,
  nslot : Int32,
  _total : Int32,
) -> Int32 {
  let mut pick = -1
  let mut best = 1 << 20
  for i in 0..<nslot {
    let mut k = 0
    for v in 0..<rad {
      if dmask[i * rad + v] {
        k = k + 1
      }
    }
    if k == 0 {
      return 0
    }
    if k > 1 && k < best {
      best = k
      pick = i
    }
  }
  if pick < 0 {
    return 1
  }
  let mut acc = 0
  for v in 0..<rad {
    if dmask[pick * rad + v] {
      let nxt : Array[Bool] = []
      for i in 0..<(nslot * rad) {
        nxt.push(dmask[i])
      }
      for w in 0..<rad {
        nxt[pick * rad + w] = w == v
      }
      if b8_ac3(nxt, cA, cB, cF, rad, nslot, _total) {
        acc = acc + b8_count_sol(nxt, cA, cB, cF, rad, nslot, _total)
      }
    }
  }
  acc
}

///|
/// |Nat(F, G)|：以「插槽 + 自然性約束 + AC-3 剪枝 + 回溯」精確計數。
pub fn b8_nat_count(f : B8PS, g : B8PS) -> Int32 {
  let cat = f.cat
  let mx = f.mx
  let fmx = f.mx
  let gmx = g.mx
  let total = cat.nob * mx
  let rad = gmx
  // 插槽編號重排：只保留真正的插槽
  let slotidx : Array[Int32] = []
  for _ in 0..<total {
    slotidx.push(-1)
  }
  let mut nslot = 0
  for cc in 0..<cat.nob {
    for i in 0..<f.sz[cc] {
      slotidx[cc * mx + i] = nslot
      nslot = nslot + 1
    }
  }
  let dmask : Array[Bool] = []
  for _ in 0..<(nslot * rad) {
    dmask.push(false)
  }
  for cc in 0..<cat.nob {
    for i in 0..<f.sz[cc] {
      let sl = slotidx[cc * mx + i]
      for v in 0..<g.sz[cc] {
        dmask[sl * rad + v] = true
      }
    }
  }
  let cA : Array[Int32] = []
  let cB : Array[Int32] = []
  let cF : Array[Int32] = []
  for m in 0..<cat.nmor {
    let b = cat.cod[m]
    for i in 0..<f.sz[b] {
      cA.push(slotidx[cat.dom[m] * mx + f.res[m * fmx + i]])
      cB.push(slotidx[b * mx + i])
      for v in 0..<rad {
        cF.push(if v < g.sz[b] { g.res[m * gmx + v] } else { 0 })
      }
    }
  }
  if !b8_ac3(dmask, cA, cB, cF, rad, nslot, total) {
    return 0
  }
  b8_count_sol(dmask, cA, cB, cF, rad, nslot, total)
}
// ───────────────────────── 點函子的核對 ─────────────────────────

///|
/// 對每個物件跑一個述詞。
fn b8_for_all_objects(cat : B8Cat, p : (Int32) -> Bool) -> Bool {
  for c in 0..<cat.nob {
    if !p(c) {
      return false
    }
  }
  true
}

///|
/// 點函子 ev_c 的五項交叉核對（全部以 Nat 集計數實現）：
///   (1) Yoneda：|Nat(よc, F)| = |F(c)|
///   (2) 保乘積：|Nat(よc, F×G)| = |Nat(よc,F)|·|Nat(よc,G)| = |F(c)|·|G(c)|
///   (3) 保餘積：|Nat(よc, F⊔G)| = |Nat(よc,F)| + |Nat(よc,G)| = |F(c)|+|G(c)|
///   (4) 左伴隨：|Nat(A⊗よc, F)| = |F(c)|^A
///   (5) 右伴隨：|Nat(F, G_A)| = A^{|F(c)|}
pub fn b8_point_functor_checks(
  cat : B8Cat,
  seed : Int64,
) -> (Bool, Bool, Bool, Bool, Bool) {
  let f = b8_ps_rand(cat, seed)
  let g = b8_ps_rand(cat, seed + 17L)
  let a = 2
  let yoneda_ok = b8_for_all_objects(cat, fn(cc) -> Bool {
    b8_nat_count(b8_ps_yoneda(cat, cc), f) == f.sz[cc]
  })
  let prod_ok = b8_for_all_objects(cat, fn(cc) -> Bool {
    let y = b8_ps_yoneda(cat, cc)
    let lhs = b8_nat_count(y, b8_ps_prod(f, g))
    lhs == f.sz[cc] * g.sz[cc]
  })
  let coprod_ok = b8_for_all_objects(cat, fn(cc) -> Bool {
    let y = b8_ps_yoneda(cat, cc)
    let lhs = b8_nat_count(y, b8_ps_coprod(f, g))
    lhs == f.sz[cc] + g.sz[cc]
  })
  let left_adj_ok = b8_for_all_objects(cat, fn(cc) -> Bool {
    b8_nat_count(b8_ps_free_yoneda(cat, cc, a), f) == b8_pow_int(f.sz[cc], a)
  })
  let right_adj_ok = b8_for_all_objects(cat, fn(cc) -> Bool {
    b8_nat_count(f, b8_ps_cofree(cat, cc, a)) == b8_pow_int(a, f.sz[cc])
  })
  (yoneda_ok, prod_ok, coprod_ok, left_adj_ok, right_adj_ok)
}

///|
/// |Nat(よa, よb)| 應等於 |Hom(a,b)|（Yoneda 嵌入全忠實）。
pub fn b8_yoneda_full_faithful(cat : B8Cat) -> Bool {
  let mut ok = true
  for a in 0..<cat.nob {
    for b in 0..<cat.nob {
      let lhs = b8_nat_count(b8_ps_yoneda(cat, a), b8_ps_yoneda(cat, b))
      if lhs != b8_hom(cat, a, b).length() {
        ok = false
      }
    }
  }
  ok
}

///|
/// 預層的全部元素數 Σ_v F(v)（切片 E/F 的物件數；批次九、十共用）。
pub fn b8_ps_total_sz(f : B8PS) -> Int32 {
  let mut t = 0
  for v in 0..<f.cat.nob {
    t = t + f.sz[v]
  }
  t
}
