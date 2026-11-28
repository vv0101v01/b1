///|
/// geom9.mbt — 批次九·模組 4：幾何態射（geometric morphism）
///
/// 連續映射 f : Y → X 誘導開集範疇之間的函子 u : O(X) → O(Y)，u(V) = f⁻¹(V)。
/// 幾何態射 f : Sh(Y) → Sh(X) 由兩部分組成：
///     f_* = u^pre  （直接像，右伴隨，保極限）
///     f*  = a_Y ∘ Lan_u  （逆像，左伴隨，保有限極限）
/// 這裡全部以有限計數核對：
///     伴隨：|Nat_Y(f*F, G)| = |Nat_X(F, f_*G)|
///     保終物件、保乘積：f*(1) = 1、|f*(F×G)| = |f*F|·|f*G|
///     直接像保層：f_*G 在 X 上仍是層
///     等價：不可分空間與單點空間給出等價的拓撲斯

///|
/// 連續映射 f : Y → X（fmap[y] = x）誘導的函子 u : O(X) → O(Y)。
/// 要求 f 的像稠密（每個非空開的 preimage 非空），否則 u 會打到空開集
/// （空開集不在站中；層在空開集上恆為單點，此情形另行處理）。
pub fn b9_open_fun(fmap : Array[Int32], sx : B9Site, sy : B9Site) -> B8Fun {
  let onobj : Array[Int32] = []
  for v in 0..<sx.cat.nob {
    // pre(V) = { y : fmap[y] ∈ V }
    let op : Array[Bool] = []
    for y in 0..<sy.top.npt {
      op.push(sx.top.opens[sx.opens[v]][fmap[y]])
    }
    let mut hit = -1
    for w in 0..<sy.cat.nob {
      if b_sh_arr_eq(sy.top.opens[sy.opens[w]], op) {
        hit = w
      }
    }
    onobj.push(hit)
  }
  let onmor : Array[Int32] = []
  for m in 0..<sx.cat.nmor {
    let d = sx.cat.dom[m]
    let c = sx.cat.cod[m]
    onmor.push(b9_site_incl(sy, onobj[d], onobj[c]))
  }
  b8_fun(sx.cat, sy.cat, onobj, onmor)
}

///|
/// 連續性：每個開集的 preimage 是開集（在 sy 中找得到）。
pub fn b9_cont_ok(fmap : Array[Int32], sx : B9Site, sy : B9Site) -> Bool {
  for v in 0..<sx.cat.nob {
    let op : Array[Bool] = []
    for y in 0..<sy.top.npt {
      op.push(sx.top.opens[sx.opens[v]][fmap[y]])
    }
    if b9_pop(op) == 0 {
      return false
    }
    if b9_top_find(sy.top, op) < 0 {
      return false
    }
  }
  true
}

///|
/// 直接像 f_* G = G ∘ u。
pub fn b9_direct(u : B8Fun, g : B8PS) -> B8PS {
  b8_pull(u, g)
}

///|
/// 逆像 f* F = a_Y(Lan_u F)。
pub fn b9_inverse(u : B8Fun, gy : B9Groth, f : B8PS) -> B8PS {
  b9_sheafify(gy, b8_lan(u, f))
}

///|
/// 幾何態射的伴隨核對：回傳 (|Nat_Y(f*F, G)|, |Nat_X(F, f_*G)|)。
pub fn b9_geom_adjoint(
  u : B8Fun,
  gy : B9Groth,
  f : B8PS,
  g : B8PS,
) -> (Int32, Int32) {
  (b8_nat_count(b9_inverse(u, gy, f), g), b8_nat_count(f, b9_direct(u, g)))
}

///|
/// 逆像保終物件：f*(1) 逐物件等於單點。
pub fn b9_preserves_terminal(u : B8Fun, gy : B9Groth) -> Bool {
  let one_y = b8_ps_const(u.dst, 1)
  let f = b9_inverse(u, gy, b8_ps_const(u.src, 1))
  for v in 0..<u.dst.nob {
    if f.sz[v] != one_y.sz[v] {
      return false
    }
  }
  true
}

///|
/// 逆像保乘積：|f*(F×G)| = |f*F|·|f*G| 逐物件。
pub fn b9_preserves_prod(u : B8Fun, gy : B9Groth, f : B8PS, g : B8PS) -> Bool {
  let lhs = b9_inverse(u, gy, b8_ps_prod(f, g))
  let a = b9_inverse(u, gy, f)
  let b = b9_inverse(u, gy, g)
  for v in 0..<u.dst.nob {
    if lhs.sz[v] != a.sz[v] * b.sz[v] {
      return false
    }
  }
  true
}

///|
/// 直接像保層：G 是 Y 上的層 ⟹ f_*G 是 X 上的層。
pub fn b9_direct_preserves_sheaf(u : B8Fun, gx : B9Groth, g : B8PS) -> Bool {
  b9_is_sheaf(gx, b9_direct(u, g))
}

///|
/// 單點空間。
pub fn b9_pt() -> B9Top {
  b9_top(1, [[false], [true]])
}

///|
/// 不可分空間（兩個點、只有 ∅ 與 X 兩個開集）。
pub fn b9_indiscrete(n : Int32) -> B9Top {
  let all : Array[Bool] = []
  let none : Array[Bool] = []
  for _ in 0..<n {
    all.push(true)
    none.push(false)
  }
  b9_top(n, [none, all])
}
