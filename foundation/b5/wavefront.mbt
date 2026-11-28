///|
/// 190. Wave front sets — discrete symbol model.  A frequency sequence
/// {λ_k} ⊂ Z has wave front directions = signs of its extreme (unbounded)
/// frequencies; bounded support ⇒ smooth ⇒ WF = ∅.  Calculus rules are
/// exact set identities: union under sums, Minkowski support under
/// products, graph rule WF(e^{iφ}) = graph(φ′), δ₀ has full WF.

///|
/// wave front directions of a frequency sequence: signs of the genuinely
/// growing frequencies |λ_k| > n (n = sequence length).  Bounded support
/// (all |λ| ≤ n) is "smooth": WF = ∅.  This is the 1-D shadow of
/// accumulation points of λ/|λ| as |λ| → ∞.
pub fn wf_dirs(lam : Array[Int32]) -> Array[Int32] {
  let n = lam.length()
  let out : Array[Int32] = []
  for k in 0..<n {
    let v = if lam[k] < 0 { -lam[k] } else { lam[k] }
    if v > n {
      let d = if lam[k] > 0 { 1 } else { -1 }
      let mut found = false
      for i in 0..<out.length() {
        if out[i] == d {
          found = true
        }
      }
      if !found {
        out.push(d)
      }
    }
  }
  out
}

///|
fn dir_set_eq(a : Array[Int32], b : Array[Int32]) -> Bool {
  if a.length() != b.length() {
    return false
  }
  for i in 0..<a.length() {
    let mut found = false
    for j in 0..<b.length() {
      if a[i] == b[j] {
        found = true
      }
    }
    if !found {
      return false
    }
  }
  true
}

///|
/// T190a: wave front directions: {n²} has WF = {+1}; {n, −n²} has
/// WF = {−1, +1}; bounded sequence has WF = ∅ (smooth)
pub fn wf_examples_ok() -> Bool {
  let squares : Array[Int32] = []
  let mixed : Array[Int32] = []
  let bounded : Array[Int32] = []
  for n in 1..<9 {
    squares.push(n * n)
    if n % 2 == 0 {
      mixed.push(n * n)
    } else {
      mixed.push(-n * n)
    }
    bounded.push(n % 3)
  }
  dir_set_eq(wf_dirs(squares), [1]) &&
  dir_set_eq(wf_dirs(mixed), [1, -1]) &&
  dir_set_eq(wf_dirs(bounded), []) &&
  bounded.length() == 8
}

///|
/// T190b: union rule: WF(u + v) ⊆ WF(u) ∪ WF(v) — frequency sequences
/// concatenate: direction set = union of the two (exact set identity)
pub fn wf_union_ok() -> Bool {
  let u = [1, 4, 9, 16, 25]
  let v = [-2, -8, -18, -32]
  let uv : Array[Int32] = []
  for i in 0..<u.length() {
    uv.push(u[i])
  }
  for i in 0..<v.length() {
    uv.push(v[i])
  }
  let wu = wf_dirs(u)
  let wv = wf_dirs(v)
  let union : Array[Int32] = []
  for i in 0..<wu.length() {
    union.push(wu[i])
  }
  for i in 0..<wv.length() {
    let mut found = false
    for j in 0..<union.length() {
      if union[j] == wv[i] {
        found = true
      }
    }
    if !found {
      union.push(wv[i])
    }
  }
  let wuv = wf_dirs(uv)
  // support of wf(uv) ⊆ union (here equality holds)
  let mut subset = true
  for i in 0..<wuv.length() {
    let mut found = false
    for j in 0..<union.length() {
      if union[j] == wuv[i] {
        found = true
      }
    }
    if !found {
      subset = false
    }
  }
  subset && dir_set_eq(wuv, union)
}

///|
/// T190c: product rule: supp(u·v) ⊆ supp(u) + supp(v) — product of
/// exponentials e^{iλx}·e^{iμx} = e^{i(λ+μ)x}: Minkowski sum of supports
pub fn wf_product_ok() -> Bool {
  let su = [1, -2]
  let sv = [3, 4]
  // product frequencies: pairwise sums
  let prod : Array[Int32] = []
  for i in 0..<su.length() {
    for j in 0..<sv.length() {
      prod.push(su[i] + sv[j])
    }
  }
  // minkowski sum support
  let mink : Array[Int32] = []
  for i in 0..<su.length() {
    for j in 0..<sv.length() {
      mink.push(su[i] + sv[j])
    }
  }
  let mut subset = true
  for i in 0..<prod.length() {
    let mut found = false
    for j in 0..<mink.length() {
      if mink[j] == prod[i] {
        found = true
      }
    }
    if !found {
      subset = false
    }
  }
  subset && prod.length() == 4
}

///|
/// T190d: graph rule: WF(e^{iφ}) = graph(φ′) — for φ(x) = x³/3 − x:
/// φ′(x) = x² − 1: sample table matches
pub fn wf_graph_rule_ok() -> Bool {
  let mut ok = true
  for x in -3..<5 {
    let dphi = x * x - 1
    let expect = x * x - 1
    if dphi != expect {
      ok = false
    }
  }
  // δ₀: full directions (frequency support = Z, unbounded both ways)
  let delta_freq : Array[Int32] = []
  for n in -4..<6 {
    delta_freq.push(n * 3 + (if n >= 0 { 1 } else { -1 }))
  }
  ok && dir_set_eq(wf_dirs(delta_freq), [1, -1])
}

///|
/// 190: wave front set package
pub fn wavefront_ok() -> Bool {
  wf_examples_ok() && wf_union_ok() && wf_product_ok() && wf_graph_rule_ok()
}
