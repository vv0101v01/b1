///|
/// geo11.mbt — 批次十一·模組 2：局部／平展／連通幾何態射、依賴乘積、六運算
///
/// 沿用預層範疇的標準伴隨串（對 u : C → D）：
///     f_! = Lan_u  ⊣  f^* = u^*（前合成）  ⊣  f_* = Ran_u  ⊣  f^!
/// 其中 Ran_u 就是「依賴乘積」；f_! 是「帶緊支撐直像」。
/// 本模組在離散範疇（逐纖維乘積／逐纖維和）上把整串伴隨全部具體化並計數核對。

///|
/// 由逐物件尺寸造「非恆常」預層（限制映射取恆等），用作判據的非平凡樣本。
pub fn b11_ps_family(cat : B8Cat, sz : Array[Int32]) -> B8PS {
  let mx = b8_ps_mx_of(sz)
  let res : Array[Int32] = []
  for _ in 0..<(cat.nmor * mx) {
    res.push(0)
  }
  for m in 0..<cat.nmor {
    let v = cat.cod[m]
    for x in 0..<sz[v] {
      res[m * mx + x] = x
    }
  }
  b8_ps_make(cat, sz, res)
}

// ───────────────────────── 依賴乘積（右 Kan） ─────────────────────────

///|
/// 右 Kan 擴張（離散範疇）：(Ran_u F)(d) = ∏_{c : u(c) = d} F(c)。
pub fn b11_ran(u : B8Fun, f : B8PS) -> B8PS {
  let d = u.dst
  let sz : Array[Int32] = []
  for o in 0..<d.nob {
    let mut p = 1
    for c in 0..<u.src.nob {
      if u.onobj[c] == o {
        p = p * f.sz[c]
      }
    }
    sz.push(p)
  }
  let st : Array[Int32] = sz
  let mx = b8_ps_mx_of(st)
  let res : Array[Int32] = []
  for _ in 0..<(d.nmor * mx) {
    res.push(0)
  }
  for m in 0..<d.nmor {
    let b = d.cod[m]
    for j in 0..<sz[b] {
      res[m * mx + j] = if j < mx { j } else { 0 }
    }
  }
  b8_ps_make(d, sz, res)
}

///|
/// 逐物件最大尺寸。
fn b8_ps_mx_of(sz : Array[Int32]) -> Int32 {
  let mut m = 1
  for s in sz {
    if s > m {
      m = s
    }
  }
  m
}

///|
/// 依賴乘積的伴隨恆等式：|Nat(f^*G, F)| = |Nat(G, Ran_u F)|。
pub fn b11_dep_prod_ok(u : B8Fun, f : B8PS, g : B8PS) -> Bool {
  b8_nat_count(b8_pull(u, g), f) == b8_nat_count(g, b11_ran(u, f))
}

// ───────────────────────── 六運算 ─────────────────────────

///|
/// 六運算的核心兩條伴隨：(Lan ⊣ u^*)、Frobenius（Lan 強么半）。
pub fn b11_six_ok(u : B8Fun, a : B8PS, b : B8PS) -> (Bool, Bool) {
  let adj = b8_nat_count(b8_lan(u, a), b) == b8_nat_count(a, b8_pull(u, b))
  let frob = b8_ps_eq(
    b8_lan(u, b8_ps_prod(a, b8_pull(u, b))),
    b8_ps_prod(b8_lan(u, a), b),
  )
  (adj, frob)
}

///|
/// 三伴隨串的第三段：u^* ⊣ Ran_u（即 pull ⊣ f_*）。
pub fn b11_pull_ran_ok(u : B8Fun, f : B8PS, g : B8PS) -> Bool {
  b11_dep_prod_ok(u, f, g)
}

///|
/// 帶緊支撐直像 f_! 與直像 f_* 的規模差（係數 n）：回傳 (Σ 型, ∏ 型)。
/// 兩者相等 ⟺ 每個纖維至多一點（「真／緊」的必要條件）。
pub fn b11_sum_prod(u : B8Fun, n : Int32) -> (Int32, Int32) {
  let cst = b8_ps_const(u.src, n)
  let lan = b8_lan(u, cst)
  let ran = b11_ran(u, cst)
  let mut s = 0
  let mut p = 0
  for o in 0..<u.dst.nob {
    s = s + lan.sz[o]
    p = p + ran.sz[o]
  }
  (s, p)
}

///|
/// 「真／緊」判據：f_! = f_*（逐物件）⟺ 所有纖維的點數 ≤ 1。
pub fn b11_proper(u : B8Fun) -> Bool {
  let mut mx = 0
  for o in 0..<u.dst.nob {
    let mut c = 0
    for z in 0..<u.src.nob {
      if u.onobj[z] == o {
        c = c + 1
      }
    }
    if c > mx {
      mx = c
    }
  }
  mx <= 1
}

// ───────────────────────── 三類幾何態射 ─────────────────────────

///|
/// 連通幾何態射：f^* 全忠實（|Nat(F,G)| = |Nat(f^*F, f^*G)|）。
pub fn b11_connected(u : B8Fun, xs : Array[B8PS], ys : Array[B8PS]) -> Bool {
  for x in xs {
    for y in ys {
      if b8_nat_count(x, y) != b8_nat_count(b8_pull(u, x), b8_pull(u, y)) {
        return false
      }
    }
  }
  true
}

///|
/// 平展幾何態射（切片型）：f_! ⊣ f^* 且 Wirthmüller 型同構
/// f_!(A ⊗ f^*B) = f_!A ⊗ B（Frobenius）。
pub fn b11_etale(u : B8Fun, a : B8PS, b : B8PS) -> Bool {
  let (adj, frob) = b11_six_ok(u, a, b)
  adj && frob
}

///|
/// 局部幾何態射：f_* 有右伴隨 f^!，候選構造 f^! = u^*（逐物件右伴隨）。
/// 伴隨恆等式 |Nat(Ran_u F, G)| = |Nat(F, f^!G)| 在 u 為範疇等價時成立。
pub fn b11_local_ok(u : B8Fun, f : B8PS, g : B8PS) -> Bool {
  b8_nat_count(b11_ran(u, f), g) == b8_nat_count(f, b8_pull(u, g))
}
