use prusti_contracts::*;

enum List {
    Cons(i32, Box<List>),
    Nil
}

// #[requires(f |= |arg: i32| -> i32 [ requires(list_contains(v, arg)) ])]
// #[ensures(list_len(&result) == old(list_len(v)))]
// #[ensures(
//     forall(|idx: usize| 0 <= idx && idx < list_len(v)
//         ==> f ~> |arg: i32| -> i32
//             { arg == list_nth(v, idx) }
//             { cl_result == list_nth(&result, idx) })
// )]
fn map<F: FnMut(i32) -> i32>(v: &List, f: &mut F) -> List {
    match v {
        List::Cons(value, tail) => {
            List::Cons(f(*value), Box::new(map(tail, f)))
        }
        List::Nil => List::Nil,
    }
}

// #[requires(list_len(v) == 3)]
// #[requires(list_nth(v, 0) == 1)]
// #[requires(list_nth(v, 1) == 2)]
// #[requires(list_nth(v, 2) == 3)]
// fn test1(v: &List) {
//     let mut cl = closure!(
//         #[requires(true)]
//         #[ensures(result == i * 3)]
//         |i: i32| -> i32 { i * 3 }
//     );

//     let res = map(&v, &mut cl);
//     assert!(list_nth(&res, 0) == 3);
//     assert!(list_nth(&res, 1) == 6);
//     assert!(list_nth(&res, 2) == 9);
// }

// #[requires(vec_len(v) == 3)]
// #[requires(vec_lookup(v, 0) == 1)]
// #[requires(vec_lookup(v, 1) == 2)]
// #[requires(vec_lookup(v, 2) == 3)]
// fn test2(v: &Vec<i32>) {
//     let mut x = 7;
//     let mut cl = closure!(
//         #[view(x: i32)]
//         #[requires(true)]
//         #[invariant(*views.x >= 0)]
//         #[invariant(*views.x >= old(*views.x))]
//         #[ensures(result == old(*views.x))]
//         #[ensures(*views.x == old(*views.x) + 1)]
//         |i: i32| -> i32 { let r = x; x += 1; r }
//     );

//     // spec does not specify order of calls, so res[0] == 7 cannot be proven
//     let res = map_vec(&v, &mut cl);
//     assert!(vec_lookup(&res, 0) >= 7);
//     assert!(vec_lookup(&res, 1) >= 7);
//     assert!(vec_lookup(&res, 2) >= 7);
// }

fn main() {}

// Prusti glue for List
    #[pure]
    #[trusted]
    fn list_contains(xs: &List, val: i32) -> bool {
        match xs {
            List::Cons(h, t) => { *h == val || list_contains(t, val) }
            List::Nil => false
        }
    }

    // #[pure]
    // #[trusted]
    // fn list_len(xs: &List) -> usize {
    //     match xs {
    //         List::Cons(h, t) => { 1 + list_len(t) }
    //         List::Nil => 0
    //     }
    // }

    // #[pure]
    // #[trusted]
    // fn list_nth(xs: &List, idx: usize) -> i32 {
    //     match xs {
    //         List::Cons(h, t) => {
    //             if idx == 0 {
    //                 *h
    //             } else {
    //                 list_nth(t, idx)
    //             }
    //         }
    //         List::Nil => -1
    //     }
    // }

// Prusti glue for Vec<i32>
    // #[trusted]
    // #[ensures(vec_len(&result) == 0)]
    // fn vec_new() -> Vec<i32> {
    //     vec![]
    // }

    // #[pure]
    // #[trusted]
    // #[ensures(result >= 0)]
    // fn vec_len(vec: &Vec<i32>) -> usize {
    //     vec.len()
    // }

    // #[pure]
    // #[trusted]
    // #[requires(idx >= 0 && idx < vec_len(vec))]
    // #[ensures(vec_contains(vec, result))]
    // fn vec_lookup(vec: &Vec<i32>, idx: usize) -> i32 {
    //     vec[idx]
    // }

    // #[pure]
    // #[trusted]
    // fn vec_contains(vec: &Vec<i32>, val: i32) -> bool {
    //     vec.contains(&val)
    // }

    // #[trusted]
    // #[ensures(vec_len(vec) == old(vec_len(vec)) + 1)]
    // #[ensures(
    //     forall(|idx: usize| 0 <= idx && idx < old(vec_len(vec))
    //         ==> vec_lookup(vec, idx) == old(vec_lookup(vec, idx)),
    //         triggers = [(vec_lookup(vec, idx),)])
    // )]
    // #[ensures(vec_lookup(vec, old(vec_len(vec))) == value)]
    // #[ensures(vec_contains(vec, value))]
    // fn vec_push(vec: &mut Vec<i32>, value: i32) {
    //     vec.push(value);
    // }
// end Prusti glue
