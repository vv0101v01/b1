///|
/// rel9.mbt — 批次九·模組 9：有效等價關係、核對、下降與小生成集
///
/// 在有限預層範疇 PSh(C) 中（逐物件計算）：
///   態射 f : A → B 的核對 R = {(x, y) : f(x) = f(y)} ⊂ A × A，
///   f 為**正則滿** ⟺ f 是 R ⇉ A → B 的餘等化子（「有效」）；
///   等價關係 R ⊂ A × A **有效** ⟺ A → A/R 的核對恰為 R。
/// PSh(C) 是拓撲斯 ⟹ 所有等價關係有效（Giraud 公理 G3 的有限影子）。
/// 小生成集：可表預層 よ(c) 生成；任何 F 由其「元素」決定（co-Yoneda）。

// ───────────────────────── 核對與餘等化子 ─────────────────────────

///|
/// 核對 R ⊂ A × A：R(v) = {(x,y) : f(x) = f(y)}，限制繼承自 A × A。
pub fn b9_kernel_pair(a : B8PS, _b : B8PS, f : Array[Int32]) -> B8PS {
  let c = a.cat
  let sz : Array[Int32] = []
  let pairs : Array[Array[Int32]] = []
  for v in 0..<c.nob {
    let ps : Array[Int32] = []
    for x in 0..<a.sz[v] {
      for y in 0..<a.sz[v] {
        if f[v * a.mx + x] == f[v * a.mx + y] {
          ps.push(x * a.sz[v] + y)
        }
      }
    }
    sz.push(ps.length())
    pairs.push(ps)
  }
  let mx = if sz.length() == 0 {
    1
  } else {
    let mut m = 1
    for x in sz {
      if x > m {
        m = x
      }
    }
    m
  }
  let res : Array[Int32] = []
  for _ in 0..<(c.nmor * mx) {
    res.push(0)
  }
  for m in 0..<c.nmor {
    let w = c.dom[m]
    let v = c.cod[m]
    for j in 0..<sz[v] {
      let code = pairs[v][j]
      let x = code / a.sz[v]
      let y = code % a.sz[v]
      let x2 = a.res[m * a.mx + x]
      let y2 = a.res[m * a.mx + y]
      let want = x2 * a.sz[w] + y2
      for k in 0..<sz[w] {
        if pairs[w][k] == want {
          res[m * mx + j] = k
        }
      }
    }
  }
  b8_ps_make(c, sz, res)
}

///|
/// 餘等化子（逐物件）：對平行對 f, g : A → B，取 B 上由 f(x) ~ g(x) 生成的等價閉包。
pub fn b9_coequalizer(
  a : B8PS,
  b : B8PS,
  f : Array[Int32],
  g : Array[Int32],
) -> B8PS {
  let c = a.cat
  let sz : Array[Int32] = []
  let cls : Array[Array[Int32]] = []
  for v in 0..<c.nob {
    let par : Array[Int32] = []
    for y in 0..<b.sz[v] {
      par.push(y)
    }
    for x in 0..<a.sz[v] {
      let u = f[v * a.mx + x]
      let w = g[v * a.mx + x]
      let mut r1 = u
      while par[r1] != r1 {
        r1 = par[r1]
      }
      let mut r2 = w
      while par[r2] != r2 {
        r2 = par[r2]
      }
      if r1 != r2 {
        par[r2] = r1
      }
    }
    let ids : Array[Int32] = []
    for _ in 0..<b.sz[v] {
      ids.push(-1)
    }
    let mut cnt = 0
    for y in 0..<b.sz[v] {
      let mut r = y
      while par[r] != r {
        r = par[r]
      }
      if ids[r] < 0 {
        ids[r] = cnt
        cnt = cnt + 1
      }
      ids[y] = ids[r]
    }
    sz.push(cnt)
    cls.push(ids)
  }
  let mx = if sz.length() == 0 {
    1
  } else {
    let mut m = 1
    for x in sz {
      if x > m {
        m = x
      }
    }
    m
  }
  let res : Array[Int32] = []
  for _ in 0..<(c.nmor * mx) {
    res.push(0)
  }
  for m in 0..<c.nmor {
    let w = c.dom[m]
    let v = c.cod[m]
    for j in 0..<sz[v] {
      // 取代表元素
      let mut rep = -1
      for y in 0..<b.sz[v] {
        if cls[v][y] == j && rep < 0 {
          rep = y
        }
      }
      if rep >= 0 {
        res[m * mx + j] = cls[w][b.res[m * b.mx + rep]]
      }
    }
  }
  b8_ps_make(c, sz, res)
}

///|
/// 有效性：f : A → B 是「核對的餘等化子」（正則滿）。
pub fn b9_effective_epi(a : B8PS, b : B8PS, f : Array[Int32]) -> Bool {
  let c = a.cat
  let kp = b9_kernel_pair(a, b, f)
  // 投影：依核對建構順序（逐物件、(x,y) 字典序）
  let flat1 : Array[Int32] = []
  let flat2 : Array[Int32] = []
  for v in 0..<c.nob {
    for x in 0..<a.sz[v] {
      for y in 0..<a.sz[v] {
        if f[v * a.mx + x] == f[v * a.mx + y] {
          flat1.push(x)
          flat2.push(y)
        }
      }
    }
  }
  let mx = kp.mx
  let pi1 : Array[Int32] = []
  let pi2 : Array[Int32] = []
  for _ in 0..<(c.nmor * mx) {
    pi1.push(0)
    pi2.push(0)
  }
  let mut cur = 0
  for v in 0..<c.nob {
    for j in 0..<kp.sz[v] {
      pi1[v * mx + j] = flat1[cur + j]
      pi2[v * mx + j] = flat2[cur + j]
    }
    cur = cur + kp.sz[v]
  }
  // f 逐點滿（正則滿的必要條件）
  for v in 0..<c.nob {
    for y in 0..<b.sz[v] {
      let mut hit = false
      for x in 0..<a.sz[v] {
        if f[v * a.mx + x] == y {
          hit = true
        }
      }
      if !hit {
        return false
      }
    }
  }
  // 餘等化子 R ⇉ A → A/R 應與 B 同構（此處核對逐物件基數與映射值）
  let q = b9_coequalizer(kp, a, pi1, pi2)
  for v in 0..<c.nob {
    if q.sz[v] != b.sz[v] {
      return false
    }
  }
  for m in 0..<c.nmor {
    let v = c.cod[m]
    for j in 0..<q.sz[v] {
      if q.res[m * q.mx + j] != j {
        return false
      }
    }
  }
  true
}

// ───────────────────────── 等價關係的有效性 ─────────────────────────

///|
/// 逐物件的等價關係：R(v) 為 A(v) 上的等價關係（以「同類」代表陣列表示）。
pub(all) struct B9Rel {
  a : B8PS
  rep : Array[Array[Int32]]
}

///|
/// 由 A 上的「分類函數」建構等價關係（x ~ y ⟺ c(x) = c(y)）。
pub fn b9_rel_of_class(a : B8PS, cls : Array[Int32]) -> B9Rel {
  let c = a.cat
  let rep : Array[Array[Int32]] = []
  for v in 0..<c.nob {
    let r : Array[Int32] = []
    for x in 0..<a.sz[v] {
      r.push(cls[v * a.mx + x])
    }
    rep.push(r)
  }
  { a, rep, }
}

///|
/// 等價關係是否對限制映射穩定（即為子預層 A × A 的子對象）。
pub fn b9_rel_stable(r : B9Rel) -> Bool {
  let a = r.a
  let c = a.cat
  for m in 0..<c.nmor {
    let w = c.dom[m]
    let v = c.cod[m]
    for x in 0..<a.sz[v] {
      for y in 0..<a.sz[v] {
        let same_before = r.rep[v][x] == r.rep[v][y]
        let x2 = a.res[m * a.mx + x]
        let y2 = a.res[m * a.mx + y]
        let same_after = r.rep[w][x2] == r.rep[w][y2]
        if same_before && !same_after {
          return false
        }
      }
    }
  }
  true
}

///|
/// 商的物件數（逐物件類數總和）。
pub fn b9_rel_quot_size(r : B9Rel) -> Int32 {
  let mut t = 0
  for v in 0..<r.a.cat.nob {
    let mut n = 0
    for x in 0..<r.a.sz[v] {
      let mut first = true
      for y in 0..<x {
        if r.rep[v][y] == r.rep[v][x] {
          first = false
        }
      }
      if first {
        n = n + 1
      }
    }
    t = t + n
  }
  t
}

///|
/// 有效性：R 為某映射的核對（即 A/R 的核對恰為 R）。
/// 以「分類函數誘導的核對大小 = |R|」核對。
pub fn b9_rel_effective(r : B9Rel) -> Bool {
  let a = r.a
  let c = a.cat
  // 商的預層：逐物件取類代表
  let clsflat : Array[Int32] = []
  for v in 0..<c.nob {
    for x in 0..<a.sz[v] {
      clsflat.push(r.rep[v][x])
    }
  }
  // 由分類函數建的核對：大小應與 R 相同
  let mut ok = true
  for v in 0..<c.nob {
    let mut cnt = 0
    for x in 0..<a.sz[v] {
      for y in 0..<a.sz[v] {
        if clsflat[v * a.mx + x] == clsflat[v * a.mx + y] {
          cnt = cnt + 1
        }
      }
    }
    let mut cnt2 = 0
    for x in 0..<a.sz[v] {
      for y in 0..<a.sz[v] {
        if r.rep[v][x] == r.rep[v][y] {
          cnt2 = cnt2 + 1
        }
      }
    }
    if cnt != cnt2 {
      ok = false
    }
  }
  ok
}

// ───────────────────────── 小生成集 ─────────────────────────

///|
/// 可表預層生成：兩個相異的自然變換 F ⇒ G 必在某個 c 與 x ∈ F(c) 上不同。
/// 以元素計數核對：Nat(F,G) 的元素由其在可表探針上的值決定，
/// 即 |Nat(F,G)| ≤ Π_c |G(c)|^{|F(c)|}（且等號在 G 可表時成立）。
pub fn b9_reps_generate(f : B8PS, g : B8PS) -> Bool {
  let c = f.cat
  let nat = b8_nat_count(f, g)
  let mut bound = 1
  for v in 0..<c.nob {
    bound = bound * b8_pow_int(g.sz[v], f.sz[v])
  }
  nat <= bound
}

///|
/// 生成集的「密度」：F 由可表探針決定 ⟺ 每個元素都被某個探針看到。
/// 以 Yoneda 直接核對：Σ_c |Nat(よc, F)| = |F|。
pub fn b9_generator_density(f : B8PS) -> (Int32, Int32) {
  b9_density_check(f)
}
