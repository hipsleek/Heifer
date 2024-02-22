use prusti_contracts::*;

#[derive(PartialEq)]
enum List {
    Cons(i32, Box<List>),
    Nil
}

// thread 'rustc' panicked at 'not implemented: ty=Closure(DefId(0:5 ~ closure[317d]::test::{closure#0}), [i32, extern "rust-call" fn((i32,)), (List,)])', analysis/src/abstract_domains/place_utils.rs:81:17
// fn test() {
//   let mut a = List::Nil;
//   let b = |x| { a = List::Cons (x, Box::new(a)) };
// }

// thread 'rustc' panicked at 'index out of bounds: the len is 0 but the index is 0', prusti-viper/src/encoder/mir_encoder.rs:175:58
// #[ensures(result > 0)]
// fn test() -> i32 {
//   let mut a = 0;
//   let mut b = closure!( #[ensures(result > 0)] || -> i32 { a = a + 1; a });
//   b()
// }

// #[ensures(result >= 3)]
// fn test() -> i32 {
//   let mut x = 0;
//   let mut b = closure!(
//     #[view(x: i32)]
//     #[invariant(*views.x >= 0)]
//     #[invariant(old(*views.x) <= *views.x)]
//     #[ensures(old(*views.x) + 1 == *views.x)]
//     #[ensures(result == old(*views.x) + 1)]
//     || -> i32 { x = x + 1; x }
//   );
//   let mut y = 0;
//   let mut c = closure!(
//     #[view(y: i32)]
//     #[invariant(*views.y >= 0)]
//     #[invariant(old(*views.y) <= *views.y)]
//     #[ensures(old(*views.y) + 2 == *views.y)]
//     #[ensures(result == old(*views.y) + 2)]
//     || -> i32 { y = y + 2; y }
//   );
//   b() + c()
// }

// error: [Prusti internal error] generating fold-unfold Viper statements failed (FailedToObtain(Pred(LabelledOld("l3", Local(_4: Ref(closure$0_17$3$9240991202403026647), Position { line: 0, column: 0, id: 0 }), Position { line: 0, column: 0, id: 71 }), read)))
// fn test() -> List {
//   let mut x = List::Nil;
//   let mut b = closure!(
//     || -> List { x = List::Cons (1, Box::new(x)); x }
//   );
//   b()
// }

#[pure]
#[trusted]
fn list_len(xs: &List) -> usize {
    match xs {
        List::Cons(h, t) => { 1 + list_len(t) }
        List::Nil => 0
    }
}

// error: [Prusti internal error] generating fold-unfold Viper statements failed (FailedToObtain(Acc(Field(Field(Local(_3: Ref(closure$0_20$3$17930834328415475987), Position { line: 81, column: 17, id: 44 }), f$x: Ref(ref$m_List$_beg_$_end_), Position { line: 81, column: 17, id: 44 }), val_ref: Ref(m_List$_beg_$_end_), Position { line: 81, column: 17, id: 44 }), read)))
// #[ensures(list_len(&*result) >= 0)]
// fn test() -> Box<List> {
//   let mut x = List::Nil;
//   let mut b = closure!(
//     #[view(x: List)]
//     #[invariant(list_len(views.x) >= 0)]
//     || -> List { x = List::Cons (1, Box::new(x)); x }
//   );
//   Box::new(b())
// }


// thread 'rustc' panicked at 'not implemented: ty=Closure(DefId(0:20 ~ closure[317d]::test::{closure#0}), [i32, extern "rust-call" fn(()) -> List, (List,)])', analysis/src/abstract_domains/place_utils.rs:81:17
// #[ensures(list_len_lb(&*result) >= 0)]
// fn test() -> Box<List> {
//   let mut x = List::Nil;
//   let mut b = closure!(
//     #[view(x: List)]
//     #[invariant(list_len_lb(views.x) >= 0)]
//     #[invariant(list_len_lb(old(views.x)) <= list_len_lb(views.x))]
//     || -> List { x = List::Cons (1, Box::new(x)); x }
//   );
//   Box::new(b())
// }

// error: [Prusti internal error] generating fold-unfold Viper statements failed (FailedToObtain(Acc(Field(Field(Local(_3: Ref(closure$0_20$3$17931320189414076947), Position { line: 83, column: 17, id: 44 }), f$x: Ref(ref$m_List$_beg_$_end_), Position { line: 83, column: 17, id: 44 }), val_ref: Ref(m_List$_beg_$_end_), Position { line: 83, column: 17, id: 44 }), read)))
// #[ensures(list_len_lb(&*result) >= 0)]
// fn test() -> Box<List> {
//   let mut x = List::Nil;
//   let mut b = closure!(
//     #[view(x: List)]
//     #[invariant(list_len_lb(views.x) >= 0)]
//     #[invariant(old(list_len_lb(views.x)) <= list_len_lb(views.x))]
//     || -> List { x = List::Cons (1, Box::new(x)); x }
//   );
//   Box::new(b())
// }



#[pure]
#[trusted]
fn list_len_lb(xs: &List) -> usize {
    match xs {
        List::Cons(h, t) => 1,
        List::Nil => 0
    }
}

// error: [Prusti internal error] unexpected verification error: [fold.failed:insufficient.permission] Folding m_List$_beg_$_end_Cons(old[l18](_14.val_ref).enum_Cons) might fail.There might be insufficient permission to access old[l18](_14.val_ref).enum_Cons (@3.10)
// #[derive(PartialEq)]
// enum List1 {
//     Cons(i32, List),
//     Nil
// }

// Infinite-sized type, which isn't allowed in Rust
// #[derive(PartialEq)]
// enum List1 {
//     Cons(i32, List1),
//     Nil
// }

// error: [Prusti: invalid specification] the type of the old expression is invalid
#[ensures(list_len_lb(&*result) >= 0)]
fn test() -> Box<List> {
  let mut x = List::Nil;
  // let mut x = List::Cons (1, Box::new(List::Nil));
  let mut b = closure!(
    #[view(x: List)]
    #[invariant(list_len_lb(views.x) >= 0)]
    // #[invariant(list_len_lb(old(views.x)) <= list_len_lb(views.x))]
    // #[ensures(old(*views.x) + 1 == *views.x)]
    // #[ensures(result == old(*views.x) + 1)]
    || -> List { x = List::Cons (1, Box::new(x)); x }
  );
  Box::new(b())
}


fn main() {}
