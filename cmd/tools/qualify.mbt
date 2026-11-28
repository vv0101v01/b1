///|
/// qualify.mbt — 把「只在 test 區塊使用」的跨套件名稱改寫成 `@als.name`（取代
/// `tools/qualify_test_uses.py`）。
///
/// 為什麼需要：編譯器的「未使用匯入」分析不計 test 區塊內的引用，因此若某名稱只在
/// `test` 內用到，它留在 `using` 就永遠被判 unused（`--deny-warn` 直接失敗），
/// 而刪掉它又會讓 test 內的裸引用失效。唯一乾淨的解是把它寫成限定形式。

///|
fn is_ident_byte(c : Char) -> Bool {
  let v = c.to_int()
  is_ident_char(v)
}

///|
/// 在純文字上把「未限定的識別字 name」換成 replacement（不做語法分析，
/// 但會避開字串／註解以外的情況一律照換——呼叫端只對 test 區塊內出現的名字使用）
fn rewrite_ident(text : String, name : String, replacement : String) -> String {
  let cs = text.to_array()
  let n = cs.length()
  let nm = name.to_array()
  let sb = StringBuilder()
  let mut i = 0
  while i < n {
    // 複製註解與字串原樣
    if cs[i].to_int() == 47 && i + 1 < n && cs[i + 1].to_int() == 47 {
      while i < n && cs[i].to_int() != 10 {
        sb.write_char(cs[i])
        i = i + 1
      }
      continue
    }
    if cs[i].to_int() == 34 {
      sb.write_char(cs[i])
      i = i + 1
      let mut closed = false
      while i < n && !closed {
        let d = cs[i].to_int()
        sb.write_char(cs[i])
        if d == 92 && i + 1 < n {
          sb.write_char(cs[i + 1])
          i = i + 2
          continue
        }
        if d == 34 {
          closed = true
        }
        i = i + 1
      }
      continue
    }
    let starts_ident = i + nm.length() <= n && matches_at(cs, i, nm)
    let prev_ok = if i == 0 {
      true
    } else {
      !is_ident_byte(cs[i - 1]) && cs[i - 1] != '.' && cs[i - 1] != '@'
    }
    let next_ok = if i + nm.length() >= n {
      true
    } else {
      !is_ident_byte(cs[i + nm.length()])
    }
    if starts_ident && prev_ok && next_ok {
      sb.write_string(replacement)
      i = i + nm.length()
      continue
    }
    sb.write_char(cs[i])
    i = i + 1
  }
  sb.to_string()
}

///|
fn matches_at(cs : Array[Char], i : Int32, nm : Array[Char]) -> Bool {
  if i + nm.length() > cs.length() {
    return false
  }
  let mut j = 0
  let mut ok = true
  while j < nm.length() {
    if cs[i + j] != nm[j] {
      ok = false
    }
    j = j + 1
  }
  ok
}

///|
/// 收集某套件中「未限定」出現的名字，分成 非 test / 僅 test 兩組
fn split_names(
  idx : Index,
  pkg : String,
) -> (Map[String, Bool], Map[String, Bool]) {
  let outside : Map[String, Bool] = Map([])
  let inside : Map[String, Bool] = Map([])
  let srcs = idx.sources.get(pkg)
  if srcs is None {
    return (outside, inside)
  }
  for src in srcs.unwrap() {
    let n = src.toks.length()
    let mut i = 0
    while i < n {
      match src.toks[i] {
        Ident(x) =>
          if !is_keyword(x) {
            let mut qual = false
            if i + 1 < n &&
              src.toks[i + 1] == Sym(':') &&
              !(i + 2 < n && src.toks[i + 2] == Sym(':')) {
              qual = true
            }
            if i > 0 {
              match src.toks[i - 1] {
                At(_) => qual = true
                Sym(c) =>
                  if c == '.' {
                    qual = true
                  } else if c == ':' && i > 1 && src.toks[i - 2] == Sym(':') {
                    qual = true
                  }
                _ => ()
              }
            }
            if !qual {
              if src.in_test[i] {
                inside[x] = true
              } else {
                outside[x] = true
              }
            }
          }
        _ => ()
      }
      i = i + 1
    }
  }
  (outside, inside)
}

///|
pub fn run_qualify(root : String, check_only : Bool) -> Unit {
  let idx = build_index(root)
  let mut moved = 0
  for p in idx.pkgs {
    if p.dir == "cmd/tools" {
      continue
    }
    let (outside, inside) = split_names(idx, p.dir)
    // 只在 test 出現在、且屬於別的套件的公開宣告 → 必須寫成 @alias.name
    let todo : Array[(String, String, String)] = [] // (alias, name, alias)
    for name, _ in inside {
      if outside.contains(name) {
        continue
      }
      match idx.decls.get(name) {
        Some(ds) => {
          let mut best : String = ""
          for d in ds {
            if d.is_pub && d.pkg != p.dir && best == "" {
              best = d.pkg
            }
          }
          if best != "" {
            todo.push((basename_als(best), name, best))
          }
        }
        None => ()
      }
    }
    if todo.length() == 0 {
      continue
    }
    for t3 in todo {
      let als = t3.0
      let name = t3.1
      println(
        (if check_only { "[漂移] " } else { "[FIX] " }) +
        p.dir +
        " : " +
        name +
        " 只在 test 中使用 → @" +
        als +
        "." +
        name,
      )
      moved = moved + 1
      if !check_only {
        for f in p.files {
          let path = root + "/" + f
          let txt = read_text(path)
          let nt = rewrite_ident(txt, name, "@" + als + "." + name)
          if nt != txt {
            write_text(path, nt)
          }
        }
      }
    }
    // 確保 zz_deps 不再列出這些名字（deps 子命令會依分析結果重寫）
  }
  if moved == 0 {
    println(
      "[PASS] qualify：沒有「只出現在 test 區塊」的裸引用（0 漂移）",
    )
  } else {
    println(
      (if check_only {
        "[FAIL] qualify：發現 "
      } else {
        "[FIX] qualify：已改寫 "
      }) +
      moved.to_string() +
      " 個名稱",
    )
  }
}

///|
fn basename_als(pkg : String) -> String {
  let a = pkg.to_array()
  let mut i = 0
  let mut last = -1
  while i < a.length() {
    if a[i] == '/' {
      last = i
    }
    i = i + 1
  }
  let sb = StringBuilder()
  let mut j = last + 1
  while j < a.length() {
    sb.write_char(a[j])
    j = j + 1
  }
  sb.to_string()
}
