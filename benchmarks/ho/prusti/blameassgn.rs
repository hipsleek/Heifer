use prusti_contracts::*;

// From Findler and Felleisen (2002)

#[requires(f |= |i: i32| -> i32 [
    requires(i > 9),
    ensures(cl_result >= 0 && cl_result <= 99)
])]
#[ensures(result >= 0 && result <= 99)]
fn g<T: FnMut(i32) -> i32>(mut f: T) -> i32 {
    f(10)
    // f(0) should cause a verification error
}

fn main() {
    let h = closure!(
        #[requires(i > 9)]
        #[ensures(result >= 50 && result <= 99)]
        |i: i32| -> i32 { 66 }
    );
    g(h);

    let f = closure!(
        #[requires(i > 9)]
        #[ensures(result >= -10 && result <= 89)]
        |i: i32| -> i32 { -10 }
    );
    // g(f); should cause a verification error
}
